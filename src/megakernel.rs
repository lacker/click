//! Experimental rich kernel for systems-code proofs.
//!
//! This module keeps the LCF shape: `Theorem` is an abstract object whose
//! constructor is not public. Public theorem constructors in this module are
//! Click axioms: trusted built-in operations that produce theorem objects
//! directly.

use std::collections::{BTreeMap, BTreeSet};

const C_POINTER_BYTE_WIDTH: u32 = 8;
const RANGE_FOLD_CONCRETE_UNROLL_LIMIT: i64 = 1024;

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
    Pointer(Pointer),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CType {
    Int32,
    Int32Pointer,
    Int32Array(u32),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLValue {
    storage: CLValueStorage,
    value_type: CType,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum CLValueStorage {
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
    Load(Box<CExpression>),
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
pub enum CProposition {
    Comparison {
        left: CExpression,
        operator: CComparisonOperator,
        right: CExpression,
    },
    And(Box<CProposition>, Box<CProposition>),
    Or(Box<CProposition>, Box<CProposition>),
    Not(Box<CProposition>),
    Implies(Box<CProposition>, Box<CProposition>),
    ForAllInt32 {
        name: String,
        variable: Variable,
        body: Box<CProposition>,
    },
    Predicate {
        name: String,
        arguments: Vec<CExpression>,
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
    proposition: CProposition,
    entry_context: Option<String>,
    preservation_context: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLoopEffectCheck {
    effect: CLoopEffect,
    span: CLoopEffectSpan,
    context: Option<String>,
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
    base: CExpression,
    start: CExpression,
    end: CExpression,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemoryRange {
    base: Pointer,
    start: Bitvector32Term,
    end: Bitvector32Term,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CParameter {
    name: String,
    c_type: CType,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunction {
    return_type: CType,
    name: String,
    parameters: Vec<CParameter>,
    body: CStatement,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionSpecification {
    state: CState,
    arguments: Vec<CExpression>,
    requires: Vec<Proposition>,
    outcome: CFunctionOutcome,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionEnvironment {
    functions: BTreeMap<String, CFunction>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CUndefinedBehavior {
    SignedOverflow,
    InvalidMemory,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRuntimeError {
    UnboundVariable(String),
    UnknownFunction(String),
    TypeMismatch,
    WrongArity { expected: usize, actual: usize },
    MissingReturn,
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
    expression_steps: usize,
    statement_steps: usize,
    function_calls: usize,
    loop_unrolls: usize,
    paths: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpressionOutcome {
    Value(CValue),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum CLValueOutcome {
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
    bindings: BTreeMap<String, CLocalBinding>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum CLocalBinding {
    Object(CValue),
    ArrayObject { element_type: CType, length: u32 },
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemory {
    blocks: BTreeMap<String, CBlock>,
    cells: BTreeMap<Pointer, CValue>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CBlock {
    size: u32,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CState {
    locals: CLocalEnvironment,
    memory: CMemory,
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
    },
    CMemoryCanStore {
        memory: CMemory,
        pointer: Pointer,
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
}

/// An abstract proven proposition produced by megakernel axioms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Theorem {
    proposition: Proposition,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Assumptions {
    condition_facts: BTreeMap<ConditionTerm, bool>,
    prop_facts: BTreeSet<Proposition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProofObligation {
    proposition: Proposition,
    context: Option<String>,
    assumable: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PathFact {
    proposition: Proposition,
    public: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecution {
    paths: Vec<SymbolicCExecutionPath>,
    limit: Option<ExecutionLimit>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecutionPath {
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CExpressionPath {
    outcome: CExpressionOutcome,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CLValuePath {
    outcome: CLValueOutcome,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CStatementExecutionPath {
    outcome: CStatementOutcome,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionPath {
    outcome: CFunctionOutcome,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CArgumentsPath {
    values: Vec<CValue>,
    outcome: Option<CFunctionOutcome>,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerificationVariableGenerator {
    next: u64,
}

impl VerificationVariableGenerator {
    fn new(start: u64) -> Self {
        Self { next: start }
    }

    fn next(&mut self) -> Variable {
        let variable = Variable(self.next);
        self.next += 1;
        variable
    }
}

impl Bitvector32Term {
    pub fn var(var: Variable) -> Self {
        Self::Variable(var)
    }

    pub fn constant(value: u32) -> Self {
        Self::Constant(value)
    }

    fn as_const(&self) -> Option<u32> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Variable(_) | Self::MemoryLoad(_, _) => None,
            Self::Add(left, right) => Some(left.as_const()?.wrapping_add(right.as_const()?)),
            Self::Subtract(left, right) => Some(left.as_const()?.wrapping_sub(right.as_const()?)),
            Self::Multiply(left, right) => Some(left.as_const()?.wrapping_mul(right.as_const()?)),
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

    fn subtract_one_base(&self) -> Option<Self> {
        match self {
            Self::Subtract(left, right) if right.as_ref() == &Self::Constant(1) => {
                Some(left.as_ref().clone())
            }
            _ => None,
        }
    }

    fn is_subtract_one(&self) -> bool {
        self.subtract_one_base().is_some()
    }

    fn add_const_base(&self, value: u32) -> Option<Self> {
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

    fn add_const_parts(&self) -> Option<(Self, u32)> {
        match self {
            Self::Add(left, right) => match (left.as_ref(), right.as_ref()) {
                (base, Self::Constant(value)) => Some((base.clone(), *value)),
                (Self::Constant(value), base) => Some((base.clone(), *value)),
                _ => None,
            },
            _ => None,
        }
    }

    fn subtract_const_parts(&self) -> Option<(Self, u32)> {
        match self {
            Self::Subtract(left, right) => match right.as_ref() {
                Self::Constant(value) => Some((left.as_ref().clone(), *value)),
                _ => None,
            },
            _ => None,
        }
    }

    fn add(left: Self, right: Self) -> Self {
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

    fn subtract(left: Self, right: Self) -> Self {
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

    fn as_const(&self) -> Option<i64> {
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

    fn add(left: Self, right: Self) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left + right),
            (Some(0), _) => right,
            (_, Some(0)) => left,
            _ => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    fn scale_int32(value: Bitvector32Term, byte_width: i64) -> Self {
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
    fn signed_less_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) < (right as i32)),
            _ => Self::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
        }
    }

    fn signed_less_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) <= (right as i32)),
            _ => Self::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
        }
    }

    fn signed_greater_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) > (right as i32)),
            _ => Self::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right)),
        }
    }

    fn signed_greater_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) >= (right as i32)),
            _ => Self::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
        }
    }

    fn equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::Bitvector32Equal(Box::new(left), Box::new(right)),
        }
    }

    fn signed_add_overflows(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_add(right as i32).1)
            }
            _ => Self::Bitvector32SignedAddOverflows(Box::new(left), Box::new(right)),
        }
    }

    fn signed_subtract_overflows(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_sub(right as i32).1)
            }
            _ => Self::Bitvector32SignedSubtractOverflows(Box::new(left), Box::new(right)),
        }
    }

    fn pointer_offset_equal(left: PointerOffsetTerm, right: PointerOffsetTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::PointerOffsetEqual(Box::new(left), Box::new(right)),
        }
    }
}

impl CType {
    fn accepts(self, value: &CValue) -> bool {
        matches!(
            (self, value),
            (Self::Int32, CValue::Int32(_)) | (Self::Int32Pointer, CValue::Pointer(_))
        )
    }

    fn byte_width(self) -> u32 {
        match self {
            Self::Int32 => 4,
            Self::Int32Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int32Array(length) => length.checked_mul(4).unwrap_or(u32::MAX),
        }
    }
}

impl CValue {
    fn c_type(&self) -> CType {
        match self {
            Self::Int32(_) => CType::Int32,
            Self::Pointer(_) => CType::Int32Pointer,
        }
    }

    fn byte_width(&self) -> u32 {
        match self {
            Self::Int32(_) => 4,
            Self::Pointer(_) => C_POINTER_BYTE_WIDTH,
        }
    }
}

impl CLValue {
    fn local(name: impl Into<String>, value_type: CType) -> Self {
        Self {
            storage: CLValueStorage::Local { name: name.into() },
            value_type,
        }
    }

    fn memory(pointer: Pointer, value_type: CType) -> Self {
        Self {
            storage: CLValueStorage::Memory { pointer },
            value_type,
        }
    }

    pub fn value_type(&self) -> CType {
        self.value_type
    }

    fn pointer(&self, state: &CState) -> Option<Pointer> {
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
    fn offset_by_int32_elements(&self, elements: Bitvector32Term) -> Self {
        Self {
            block: self.block.clone(),
            offset: PointerOffsetTerm::add(
                self.offset.clone(),
                PointerOffsetTerm::scale_int32(elements, 4),
            ),
        }
    }

    fn element_index_from_base(&self, base: &Self) -> Option<Bitvector32Term> {
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
        }
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
}

impl CLoopInvariantCheck {
    pub fn new(
        proposition: CProposition,
        entry_context: Option<String>,
        preservation_context: Option<String>,
    ) -> Self {
        Self {
            proposition,
            entry_context,
            preservation_context,
        }
    }

    pub fn proposition(&self) -> &CProposition {
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

    pub fn with_int32_array(mut self, name: impl Into<String>, length: u32) -> Self {
        self.set_int32_array(name, length);
        self
    }

    pub fn set(&mut self, name: impl Into<String>, value: CValue) {
        self.bindings
            .insert(name.into(), CLocalBinding::Object(value));
    }

    pub fn set_int32_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::Int32, length);
    }

    fn set_array_object(&mut self, name: impl Into<String>, element_type: CType, length: u32) {
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
            Some(CLocalBinding::Object(value)) => Some(value),
            Some(CLocalBinding::ArrayObject { .. }) | None => None,
        }
    }

    fn binding(&self, name: &str) -> Option<&CLocalBinding> {
        self.bindings.get(name)
    }

    fn is_array_object(&self, name: &str) -> bool {
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

    fn with_havoc_marker(mut self, variable: Variable) -> Self {
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

    fn known_value(&self, pointer: &Pointer) -> Option<CValue> {
        self.cells.get(pointer).cloned()
    }

    fn without_cell(&self, pointer: &Pointer) -> Self {
        let mut memory = self.clone();
        memory.cells.remove(pointer);
        memory
    }

    fn without_proven_distinct_cells(&self, pointer: &Pointer, assumptions: &Assumptions) -> Self {
        let mut memory = self.clone();
        memory.cells.retain(|cell_pointer, _| {
            cell_pointer.block != pointer.block
                || !pointers_proven_distinct(cell_pointer, pointer, assumptions)
        });
        memory
    }

    fn without_possible_aliasing_cells(
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

    fn first_unresolved_same_block_cell(
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

    fn local_pointer(name: &str) -> Pointer {
        Pointer {
            block: format!("local:{name}"),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn has_block(&self, block: &str) -> bool {
        self.blocks.contains_key(block)
    }

    fn can_load_concretely(&self, pointer: &Pointer, byte_width: u32) -> bool {
        self.cells.contains_key(pointer) || self.access_in_bounds(pointer, byte_width)
    }

    fn can_store_concretely(&self, pointer: &Pointer, value: &CValue) -> bool {
        self.cells.contains_key(pointer) || self.access_in_bounds(pointer, value.byte_width())
    }

    fn access_in_bounds(&self, pointer: &Pointer, byte_width: u32) -> bool {
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

    fn symbolic_int32_load(&self, pointer: &Pointer) -> CValue {
        int32(Bitvector32Term::MemoryLoad(
            Box::new(self.clone()),
            Box::new(pointer.clone()),
        ))
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

    pub fn locals(&self) -> &CLocalEnvironment {
        &self.locals
    }

    pub fn memory(&self) -> &CMemory {
        &self.memory
    }
}

impl Theorem {
    fn new(proposition: Proposition) -> Self {
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

    fn consume_expression_step(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.expression_steps, ExecutionLimit::ExpressionSteps)
    }

    fn consume_statement_step(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.statement_steps, ExecutionLimit::StatementSteps)
    }

    fn consume_function_call(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.function_calls, ExecutionLimit::FunctionCalls)
    }

    fn consume_loop_unroll(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.loop_unrolls, ExecutionLimit::LoopUnrolls)
    }

    fn consume_paths(&mut self, paths: usize) -> ExecutionResult<()> {
        if self.paths < paths {
            return Err(ExecutionLimit::Paths);
        }
        self.paths -= paths;
        Ok(())
    }
}

type ExecutionResult<T> = Result<T, ExecutionLimit>;

fn consume_budget(remaining: &mut usize, limit: ExecutionLimit) -> ExecutionResult<()> {
    if *remaining == 0 {
        return Err(limit);
    }
    *remaining -= 1;
    Ok(())
}

#[cfg(test)]
impl Proposition {
    fn peel_implications(&self) -> &Self {
        match self {
            Self::Implies(_, body) => body.peel_implications(),
            _ => self,
        }
    }
}

impl Assumptions {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn assume_condition(mut self, condition: ConditionTerm, value: bool) -> Self {
        if let ConditionTerm::Bitvector32Equal(left, right) = &condition {
            if let Some((left, right)) = bitvector_equality_after_additive_cancellation(left, right)
            {
                self = self.assume_condition(ConditionTerm::equal(left, right), value);
            }
        }
        self.condition_facts.insert(condition, value);
        self
    }

    pub fn assume_proposition(mut self, proposition: Proposition) -> Self {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self = self.assume_condition(condition, value);
            }
            Proposition::And(left, right) => {
                self = self.assume_proposition(*left);
                self = self.assume_proposition(*right);
            }
            Proposition::Not(body) => match *body {
                Proposition::ConditionIs(condition, value) => {
                    self = self.assume_condition(condition, !value);
                }
                body => {
                    self.prop_facts.insert(Proposition::Not(Box::new(body)));
                }
            },
            proposition => {
                self.prop_facts.insert(proposition);
            }
        }
        self
    }

    fn decide(&self, condition: &ConditionTerm) -> Option<bool> {
        match condition {
            ConditionTerm::Constant(value) => Some(*value),
            _ => {
                let simplified = self.simplify_condition_under_assumptions(condition);
                if simplified != *condition {
                    return match simplified {
                        ConditionTerm::Constant(value) => Some(value),
                        simplified => self
                            .condition_facts
                            .get(condition)
                            .copied()
                            .or_else(|| self.condition_facts.get(&simplified).copied())
                            .or_else(|| self.decide_from_order_facts(&simplified))
                            .or_else(|| self.decide_from_overflow_facts(&simplified)),
                    };
                }

                self.condition_facts
                    .get(condition)
                    .copied()
                    .or_else(|| self.decide_from_order_facts(condition))
                    .or_else(|| self.decide_from_overflow_facts(condition))
            }
        }
    }

    fn has_condition_fact(&self, condition: ConditionTerm, value: bool) -> bool {
        self.condition_facts.get(&condition) == Some(&value)
            || self.condition_facts.iter().any(|(fact, fact_value)| {
                *fact_value == value && self.condition_matches(fact, &condition)
            })
    }

    fn bitvector_terms_equal_from_facts(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }

        let mut seen = BTreeSet::new();
        let mut stack = vec![left.clone()];
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            if &term == right {
                return true;
            }
            for (condition, value) in &self.condition_facts {
                let (ConditionTerm::Bitvector32Equal(fact_left, fact_right), true) =
                    (condition, value)
                else {
                    continue;
                };
                if fact_left.as_ref() == &term {
                    stack.push(fact_right.as_ref().clone());
                }
                if fact_right.as_ref() == &term {
                    stack.push(fact_left.as_ref().clone());
                }
            }
        }

        false
    }

    fn simplify_condition_under_assumptions(&self, condition: &ConditionTerm) -> ConditionTerm {
        match condition {
            ConditionTerm::Constant(value) => ConditionTerm::Constant(*value),
            ConditionTerm::Variable(variable) => ConditionTerm::Variable(*variable),
            ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                ConditionTerm::signed_less_than(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                ConditionTerm::signed_less_equal(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                ConditionTerm::signed_greater_than(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                ConditionTerm::signed_greater_equal(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32Equal(left, right) => ConditionTerm::equal(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                ConditionTerm::signed_add_overflows(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
                ConditionTerm::signed_subtract_overflows(
                    self.simplify_bitvector_under_assumptions(left),
                    self.simplify_bitvector_under_assumptions(right),
                )
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                ConditionTerm::pointer_offset_equal(left.as_ref().clone(), right.as_ref().clone())
            }
        }
    }

    fn simplify_bitvector_under_assumptions(&self, term: &Bitvector32Term) -> Bitvector32Term {
        match term {
            Bitvector32Term::Constant(value) => Bitvector32Term::Constant(*value),
            Bitvector32Term::Variable(variable) => Bitvector32Term::Variable(*variable),
            Bitvector32Term::Add(left, right) => Bitvector32Term::add(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::Subtract(left, right) => Bitvector32Term::subtract(
                self.simplify_bitvector_under_assumptions(left),
                self.simplify_bitvector_under_assumptions(right),
            ),
            Bitvector32Term::Multiply(left, right) => {
                let left = self.simplify_bitvector_under_assumptions(left);
                let right = self.simplify_bitvector_under_assumptions(right);
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
            Bitvector32Term::If {
                condition,
                then_term,
                else_term,
            } => match self.decide(condition) {
                Some(true) => self.simplify_bitvector_under_assumptions(then_term),
                Some(false) => self.simplify_bitvector_under_assumptions(else_term),
                None => Bitvector32Term::if_then_else(
                    condition.as_ref().clone(),
                    self.simplify_bitvector_under_assumptions(then_term),
                    self.simplify_bitvector_under_assumptions(else_term),
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
                self.simplify_bitvector_under_assumptions(start),
                self.simplify_bitvector_under_assumptions(end),
                self.simplify_bitvector_under_assumptions(initial),
                *accumulator,
                *item,
                self.simplify_bitvector_under_assumptions(body),
            ),
            Bitvector32Term::MemoryLoad(memory, pointer) => {
                Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone())
            }
        }
    }

    fn order_facts_force_equal(&self, left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
        self.has_condition_fact(
            ConditionTerm::signed_less_equal(left.clone(), right.clone()),
            true,
        ) && self.has_condition_fact(
            ConditionTerm::signed_less_than(left.clone(), right.clone()),
            false,
        ) || self.has_condition_fact(
            ConditionTerm::signed_less_equal(right.clone(), left.clone()),
            true,
        ) && self.has_condition_fact(
            ConditionTerm::signed_less_than(right.clone(), left.clone()),
            false,
        ) || self.has_condition_fact(
            ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
            true,
        ) && self.has_condition_fact(
            ConditionTerm::signed_greater_than(left.clone(), right.clone()),
            false,
        ) || self.has_condition_fact(
            ConditionTerm::signed_greater_equal(right.clone(), left.clone()),
            true,
        ) && self.has_condition_fact(
            ConditionTerm::signed_greater_than(right.clone(), left.clone()),
            false,
        )
    }

    fn range_facts_force_equal(&self, left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
        let Some((variable, constant)) = bitvector_variable_and_constant(left, right) else {
            return false;
        };

        let mut range = IntegerRangeFacts::default();
        for (condition, value) in &self.condition_facts {
            let Some((fact_left, fact_right, strict)) = condition_as_order_fact(condition, *value)
            else {
                continue;
            };
            match (
                bitvector_variable(&fact_left),
                signed_bitvector_constant(&fact_right),
            ) {
                (Some(fact_variable), Some(bound)) if fact_variable == variable => {
                    let upper = if strict { bound - 1 } else { bound };
                    range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
                }
                _ => {}
            }
            match (
                signed_bitvector_constant(&fact_left),
                bitvector_variable(&fact_right),
            ) {
                (Some(bound), Some(fact_variable)) if fact_variable == variable => {
                    let lower = if strict { bound + 1 } else { bound };
                    range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
                }
                _ => {}
            }
        }

        matches!((range.lower, range.upper), (Some(lower), Some(upper)) if lower == upper && lower == constant)
    }

    fn decide_from_order_facts(&self, condition: &ConditionTerm) -> Option<bool> {
        match condition {
            ConditionTerm::PointerOffsetEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerOffsetEqual(left, right) => {
                match (left.as_ref().as_const(), right.as_ref().as_const()) {
                    (Some(left), Some(right)) => Some(left == right),
                    _ => {
                        let left_index = int32_element_index_from_offset(left);
                        let right_index = int32_element_index_from_offset(right);
                        match (left_index, right_index) {
                            (Some(left), Some(right)) => {
                                self.decide(&ConditionTerm::equal(left, right))
                            }
                            _ => None,
                        }
                    }
                }
            }
            ConditionTerm::Bitvector32Equal(left, right) if left == right => Some(true),
            ConditionTerm::Bitvector32Equal(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if self.bitvector_add_terms_proven_equal(&left, &right)
                    || self.count_fold_split_terms_proven_equal(&left, &right)
                {
                    return Some(true);
                }

                if let Some((left, right)) =
                    bitvector_equality_after_additive_cancellation(&left, &right)
                {
                    return self.decide(&ConditionTerm::equal(left, right));
                }

                if self.bitvector_terms_equal_from_facts(&left, &right)
                    || self
                        .has_condition_fact(ConditionTerm::equal(left.clone(), right.clone()), true)
                    || self
                        .has_condition_fact(ConditionTerm::equal(right.clone(), left.clone()), true)
                    || self.memory_loads_proven_equal(&left, &right)
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                        true,
                    ) && self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                        ),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                        ),
                        true,
                    )
                    || self.order_facts_force_equal(&left, &right)
                    || self.range_facts_force_equal(&left, &right)
                {
                    Some(true)
                } else if self
                    .has_condition_fact(ConditionTerm::equal(left.clone(), right.clone()), false)
                    || self.has_condition_fact(
                        ConditionTerm::equal(right.clone(), left.clone()),
                        false,
                    )
                    || bitvector_same_base_nonzero_const_offset(&left, &right)
                {
                    Some(false)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                ) && self.has_condition_fact(
                    ConditionTerm::signed_less_than(left.clone(), right.clone()),
                    false,
                ) {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                ) && self.has_condition_fact(
                    ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                    false,
                ) {
                    Some(true)
                } else if self.decide(&ConditionTerm::signed_less_than(
                    left.clone(),
                    right.clone(),
                )) == Some(true)
                    || self.decide(&ConditionTerm::signed_greater_than(
                        left.clone(),
                        right.clone(),
                    )) == Some(true)
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                        ),
                        false,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                        ),
                        false,
                    )
                {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right) if left == right => Some(false),
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) if left == right => {
                Some(false)
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right) if left == right => Some(true),
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) if left == right => {
                Some(true)
            }
            ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if self.subtract_same_const_order_fact(&left, &right, true)
                    || self.has_order_path(&left, &right, true)
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_upper_bound_below(&left, &right)
                    || self.has_successor_upper_bound_below(&left, &right)
                    || self.has_lower_bound_above(&right, &left)
                    || self.has_add_const_lower_bound_above(&right, &left)
                    || self.positive_offset_is_proven_above(&left, &right)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                ) || self.has_condition_fact(
                    ConditionTerm::signed_less_equal(right.clone(), left.clone()),
                    true,
                ) || self.order_facts_force_equal(&left, &right)
                {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if self.has_order_path(&left, &right, false)
                    || left.add_const_base(1).is_some_and(|base| {
                        self.has_condition_fact(
                            ConditionTerm::signed_less_than(base, right.clone()),
                            true,
                        )
                    })
                    || right.subtract_one_base().is_some_and(|base| {
                        let zero = Bitvector32Term::Constant(0);
                        left == zero
                            && (self.has_condition_fact(
                                ConditionTerm::signed_greater_than(base.clone(), zero.clone()),
                                true,
                            ) || self.has_lower_bound_above(&base, &zero))
                    })
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_at_or_above(&right, &left)
                    || self.has_add_const_lower_bound_at_or_above(&right, &left)
                    || self.nonnegative_offset_is_proven_at_or_above(&left, &right)
                    || self.order_facts_force_equal(&left, &right)
                {
                    Some(true)
                } else if self
                    .has_condition_fact(ConditionTerm::signed_greater_than(left, right), true)
                {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if self.has_order_path(&right, &left, true)
                    || left.add_const_base(1).is_some_and(|base| {
                        right == Bitvector32Term::Constant(0)
                            && self.has_condition_fact(
                                ConditionTerm::signed_greater_equal(
                                    base,
                                    Bitvector32Term::Constant(0),
                                ),
                                true,
                            )
                    })
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_above(&left, &right)
                    || self.has_add_const_lower_bound_above(&left, &right)
                {
                    Some(true)
                } else if self.has_condition_fact(
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                ) || self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(right.clone(), left.clone()),
                    true,
                ) || self.order_facts_force_equal(&left, &right)
                {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if self.has_order_path(&right, &left, false)
                    || left.add_const_base(1).is_some_and(|base| {
                        right == Bitvector32Term::Constant(0)
                            && self.has_condition_fact(
                                ConditionTerm::signed_greater_equal(
                                    base,
                                    Bitvector32Term::Constant(0),
                                ),
                                true,
                            )
                    })
                    || self.has_condition_fact(
                        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(right.clone(), left.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_than(left.clone(), right.clone()),
                        false,
                    )
                    || self.has_lower_bound_at_or_above(&left, &right)
                    || self.has_add_const_lower_bound_at_or_above(&left, &right)
                    || self.order_facts_force_equal(&left, &right)
                {
                    Some(true)
                } else if self
                    .has_condition_fact(ConditionTerm::signed_less_than(left, right), true)
                {
                    Some(false)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn has_order_path(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
    ) -> bool {
        let order_facts = self.condition_order_facts();
        self.has_order_path_in_facts(left, right, require_strict, &order_facts)
    }

    fn has_order_path_in_facts(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        require_strict: bool,
        order_facts: &[(Bitvector32Term, Bitvector32Term, bool)],
    ) -> bool {
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            if self.bitvector_terms_proven_equal(&current, right)
                && (!require_strict || strict_so_far)
            {
                return true;
            }
            for (edge_left, edge_right, edge_strict) in order_facts {
                if self.bitvector_terms_proven_equal(&current, edge_left) {
                    stack.push((edge_right.clone(), strict_so_far || *edge_strict));
                }
            }
        }
        false
    }

    fn condition_order_facts(&self) -> Vec<(Bitvector32Term, Bitvector32Term, bool)> {
        self.condition_facts
            .iter()
            .filter_map(|(condition, value)| condition_as_order_fact(condition, *value))
            .collect()
    }

    fn collect_derived_order_facts(
        &self,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        for proposition in &self.prop_facts {
            self.collect_derived_order_facts_from_proposition(proposition, order_facts);
        }
    }

    fn collect_derived_order_facts_from_proposition(
        &self,
        proposition: &Proposition,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                if let Some(order_fact) = condition_as_order_fact(condition, *value) {
                    order_facts.push(order_fact);
                }
            }
            Proposition::And(left, right) => {
                self.collect_derived_order_facts_from_proposition(left, order_facts);
                self.collect_derived_order_facts_from_proposition(right, order_facts);
            }
            Proposition::Implies(left, right) if self.proves_without_prop_facts(left) => {
                self.collect_derived_order_facts_from_proposition(right, order_facts);
            }
            Proposition::ForAll { .. } => {
                self.collect_finite_forall_order_facts(proposition, order_facts);
            }
            _ => {}
        }
    }

    fn collect_finite_forall_order_facts(
        &self,
        proposition: &Proposition,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        let mut variables = Vec::new();
        let body = collect_forall_chain(proposition, &mut variables);
        if variables.is_empty() {
            return;
        }
        let Some(ranges) = finite_forall_ranges(&variables, body) else {
            return;
        };
        let Some(instantiation_count) = ranges.iter().try_fold(1usize, |count, range| {
            let width = usize::try_from(range.upper - range.lower + 1).ok()?;
            count.checked_mul(width)
        }) else {
            return;
        };
        if instantiation_count > FINITE_FORALL_INSTANTIATION_LIMIT {
            return;
        }

        let mut values = Vec::with_capacity(variables.len());
        self.collect_finite_forall_order_fact_instantiations(
            body,
            &variables,
            &ranges,
            &mut values,
            order_facts,
        );
    }

    fn collect_finite_forall_order_fact_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for (variable, value) in variables.iter().zip(values.iter()) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &signed_i64_bitvector_constant(*value),
                );
            }
            self.collect_derived_order_facts_from_proposition(&instantiated, order_facts);
            return;
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            self.collect_finite_forall_order_fact_instantiations(
                body,
                variables,
                ranges,
                values,
                order_facts,
            );
            values.pop();
        }
    }

    fn has_upper_bound_below(&self, left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedLessThan(fact_left, upper), true)
                    if fact_left.as_ref() == left =>
                {
                    self.decide(&ConditionTerm::signed_less_equal(
                        upper.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                _ => false,
            })
    }

    fn has_successor_upper_bound_below(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedLessThan(fact_left, upper), true)
                    if fact_left.as_ref() == left
                        && upper
                            .as_ref()
                            .add_const_base(1)
                            .is_some_and(|base| base == *right) =>
                {
                    self.has_condition_fact(
                        ConditionTerm::equal(left.clone(), right.clone()),
                        false,
                    )
                }
                _ => false,
            })
    }

    fn subtract_same_const_order_fact(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        strict: bool,
    ) -> bool {
        let Some((left_base, left_const)) = left.subtract_const_parts() else {
            return false;
        };
        let Some((right_base, right_const)) = right.subtract_const_parts() else {
            return false;
        };
        if left_const != right_const {
            return false;
        }

        if strict {
            self.has_condition_fact(
                ConditionTerm::signed_less_than(left_base.clone(), right_base.clone()),
                true,
            ) || self.has_condition_fact(
                ConditionTerm::signed_greater_than(right_base, left_base),
                true,
            )
        } else {
            self.has_condition_fact(
                ConditionTerm::signed_less_equal(left_base.clone(), right_base.clone()),
                true,
            ) || self.has_condition_fact(
                ConditionTerm::signed_greater_equal(right_base, left_base),
                true,
            )
        }
    }

    fn has_lower_bound_above(&self, left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, lower), true)
                    if fact_left.as_ref() == left =>
                {
                    self.decide(&ConditionTerm::signed_greater_than(
                        lower.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if fact_left.as_ref() == left =>
                {
                    self.decide(&ConditionTerm::signed_greater_than(
                        lower.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                _ => false,
            })
    }

    fn has_lower_bound_at_or_above(&self, left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, lower), true)
                    if fact_left.as_ref() == left =>
                {
                    self.decide(&ConditionTerm::signed_greater_equal(
                        lower.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if fact_left.as_ref() == left =>
                {
                    self.decide(&ConditionTerm::signed_greater_equal(
                        lower.as_ref().clone(),
                        right.clone(),
                    )) == Some(true)
                }
                _ => false,
            })
    }

    fn has_add_const_lower_bound_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, lower), true)
                    if fact_left.as_ref() == &base =>
                {
                    let Some(lower) = signed_const_add(lower, addend) else {
                        return false;
                    };
                    self.decide(&ConditionTerm::signed_greater_than(lower, right.clone()))
                        == Some(true)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if fact_left.as_ref() == &base =>
                {
                    let Some(lower) = signed_const_add(lower, addend) else {
                        return false;
                    };
                    self.decide(&ConditionTerm::signed_greater_than(lower, right.clone()))
                        == Some(true)
                }
                _ => false,
            })
    }

    fn has_add_const_lower_bound_at_or_above(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let Some((base, addend)) = left.add_const_parts() else {
            return false;
        };
        self.condition_facts
            .iter()
            .any(|(fact, value)| match (fact, value) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, lower), true)
                    if fact_left.as_ref() == &base =>
                {
                    let Some(lower) = signed_const_add(lower, addend) else {
                        return false;
                    };
                    self.decide(&ConditionTerm::signed_greater_equal(lower, right.clone()))
                        == Some(true)
                }
                (ConditionTerm::Bitvector32SignedLessEqual(lower, fact_left), true)
                    if fact_left.as_ref() == &base =>
                {
                    let Some(lower) = signed_const_add(lower, addend) else {
                        return false;
                    };
                    self.decide(&ConditionTerm::signed_greater_equal(lower, right.clone()))
                        == Some(true)
                }
                _ => false,
            })
    }

    fn positive_offset_is_proven_above(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        let Some((term_base, addend)) = term.add_const_parts() else {
            return false;
        };
        if &term_base != base || signed_u32_constant(addend).is_none_or(|value| value <= 0) {
            return false;
        }
        self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) == Some(false)
    }

    fn nonnegative_offset_is_proven_at_or_above(
        &self,
        base: &Bitvector32Term,
        term: &Bitvector32Term,
    ) -> bool {
        let Some((term_base, addend)) = term.add_const_parts() else {
            return false;
        };
        if &term_base != base || signed_u32_constant(addend).is_none_or(|value| value < 0) {
            return false;
        }
        self.decide(&ConditionTerm::signed_add_overflows(
            base.clone(),
            Bitvector32Term::Constant(addend),
        )) == Some(false)
    }

    fn memory_loads_proven_equal(&self, left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
        if let Some(left) = self.resolve_memory_load_term(left) {
            return self.bitvector_terms_proven_equal(&left, right);
        }
        if let Some(right) = self.resolve_memory_load_term(right) {
            return self.bitvector_terms_proven_equal(left, &right);
        }

        let (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) = (left, right)
        else {
            return false;
        };
        if !pointers_proven_equal(left_pointer, right_pointer, self) {
            return false;
        }
        if memories_match_for_pointer_load(left_memory, right_memory, left_pointer) {
            return true;
        }
        if memories_match_for_pointer_load_under_assumptions(
            left_memory,
            right_memory,
            left_pointer,
            self,
        ) {
            return true;
        }

        self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryMutatesOnly {
                before,
                after,
                pointers,
            } => {
                let matches_order =
                    memories_match_for_pointer_load(before, right_memory.as_ref(), left_pointer)
                        && memories_match_for_pointer_load(
                            after,
                            left_memory.as_ref(),
                            left_pointer,
                        );
                let matches_reverse =
                    memories_match_for_pointer_load(before, left_memory.as_ref(), left_pointer)
                        && memories_match_for_pointer_load(
                            after,
                            right_memory.as_ref(),
                            left_pointer,
                        );
                (matches_order || matches_reverse)
                    && pointers
                        .iter()
                        .all(|pointer| pointers_proven_distinct(pointer, left_pointer, self))
            }
            Proposition::CMemoryEffectSummary {
                before,
                after,
                mutable_ranges,
            } => {
                let matches_order = memory_matches_effect_summary_endpoint(
                    before,
                    right_memory.as_ref(),
                    left_pointer,
                ) && memory_matches_effect_summary_endpoint(
                    after,
                    left_memory.as_ref(),
                    left_pointer,
                );
                let matches_reverse = memory_matches_effect_summary_endpoint(
                    before,
                    left_memory.as_ref(),
                    left_pointer,
                ) && memory_matches_effect_summary_endpoint(
                    after,
                    right_memory.as_ref(),
                    left_pointer,
                );
                (matches_order || matches_reverse)
                    && self.ranges_proven_disjoint_from_pointer(mutable_ranges, left_pointer)
            }
            _ => false,
        })
    }

    fn resolve_memory_load_term(&self, term: &Bitvector32Term) -> Option<Bitvector32Term> {
        let Bitvector32Term::MemoryLoad(memory, pointer) = term else {
            return None;
        };
        let CValue::Int32(value) = self.resolve_memory_load_value(memory, pointer)? else {
            return None;
        };
        (&value != term).then_some(value)
    }

    fn resolve_memory_load_value(&self, memory: &CMemory, pointer: &Pointer) -> Option<CValue> {
        if let Some(value) = memory.known_value(pointer) {
            return Some(value);
        }

        let mut unresolved_same_block_cell = false;
        for (cell_pointer, value) in &memory.cells {
            if cell_pointer.block != pointer.block {
                continue;
            }
            match self.decide(&ConditionTerm::pointer_offset_equal(
                cell_pointer.offset.clone(),
                pointer.offset.clone(),
            )) {
                Some(true) => return Some(value.clone()),
                Some(false) => {}
                None => unresolved_same_block_cell = true,
            }
        }

        if unresolved_same_block_cell {
            return None;
        }

        memory
            .can_load_concretely(pointer, 4)
            .then(|| memory.symbolic_int32_load(pointer))
    }

    fn decide_from_overflow_facts(&self, condition: &ConditionTerm) -> Option<bool> {
        match condition {
            ConditionTerm::Bitvector32SignedAddOverflows(left, right)
                if right.as_ref() == &Bitvector32Term::Constant(1) =>
            {
                let int_max = Bitvector32Term::Constant(i32::MAX as u32);
                let left = left.as_ref().clone();
                (self.has_condition_fact(
                    ConditionTerm::signed_less_than(left.clone(), int_max.clone()),
                    true,
                ) || self.has_upper_bound_below(&left, &int_max))
                .then_some(false)
            }
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
                if right.as_ref() == &Bitvector32Term::Constant(1) =>
            {
                let zero = Bitvector32Term::Constant(0);
                let left = left.as_ref().clone();
                (self.has_condition_fact(
                    ConditionTerm::signed_greater_than(left.clone(), zero.clone()),
                    true,
                ) || self.has_lower_bound_above(&left, &zero))
                .then_some(false)
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                if left.as_ref().is_subtract_one()
                    && right.as_ref() == &Bitvector32Term::Constant(0) =>
            {
                let Some(left_before_sub) = left.as_ref().subtract_one_base() else {
                    return None;
                };
                let zero = Bitvector32Term::Constant(0);
                (self.has_condition_fact(
                    ConditionTerm::signed_greater_than(left_before_sub.clone(), zero.clone()),
                    true,
                ) || self.has_lower_bound_above(&left_before_sub, &zero))
                .then_some(true)
            }
            _ => None,
        }
    }

    pub fn proves(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }

        if self.is_inconsistent() {
            return true;
        }

        let direct = match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide(condition) == Some(*value)
                    || self.proves_condition_from_facts(condition, *value)
            }
            Proposition::And(left, right) => self.proves(left) && self.proves(right),
            Proposition::Or(left, right) => self.proves(left) || self.proves(right),
            Proposition::Not(body) => self.proves_not(body),
            Proposition::Implies(left, right) => self
                .clone()
                .assume_proposition(left.as_ref().clone())
                .proves(right),
            Proposition::ForAll {
                sort: Sort::CInt32,
                body,
                ..
            } => self.proves_finite_forall(proposition) || self.proves(body),
            Proposition::CMemoryCanLoad { memory, pointer } => {
                self.proves_memory_access(memory, pointer, 4)
            }
            Proposition::CMemoryCanStore { memory, pointer } => {
                self.proves_memory_access(memory, pointer, 4)
            }
            _ => self.prop_facts.contains(proposition),
        };
        direct
            || self.proves_by_finite_context_split(proposition)
            || self.proves_by_disjunction_cases(proposition)
    }

    fn proves_by_disjunction_cases(&self, proposition: &Proposition) -> bool {
        if !matches!(proposition, Proposition::Or(_, _)) {
            return false;
        }

        for disjunction in &self.prop_facts {
            let mut cases = Vec::new();
            collect_or_cases(disjunction, &mut cases);
            if cases.len() < 2 || cases.len() > DISJUNCTION_CASE_LIMIT {
                continue;
            }

            let mut base = self.clone();
            base.prop_facts.remove(disjunction);
            if cases.iter().all(|case| {
                base.clone()
                    .assume_proposition(case.clone())
                    .proves(proposition)
            }) {
                return true;
            }
        }
        false
    }

    fn proves_finite_forall(&self, proposition: &Proposition) -> bool {
        let mut variables = Vec::new();
        let body = collect_forall_chain(proposition, &mut variables);
        if variables.is_empty() {
            return false;
        }
        let Some(ranges) = finite_forall_ranges(&variables, body) else {
            return false;
        };
        let Some(instantiation_count) = ranges.iter().try_fold(1usize, |count, range| {
            let width = usize::try_from(range.upper - range.lower + 1).ok()?;
            count.checked_mul(width)
        }) else {
            return false;
        };
        if instantiation_count > FINITE_FORALL_INSTANTIATION_LIMIT {
            return false;
        }

        let mut values = Vec::with_capacity(variables.len());
        self.proves_finite_forall_instantiations(body, &variables, &ranges, &mut values)
    }

    fn proves_finite_forall_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
    ) -> bool {
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for (variable, value) in variables.iter().zip(values.iter()) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &signed_i64_bitvector_constant(*value),
                );
            }
            return self.proves(&instantiated);
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            if !self.proves_finite_forall_instantiations(body, variables, ranges, values) {
                values.pop();
                return false;
            }
            values.pop();
        }
        true
    }

    fn proves_by_finite_context_split(&self, proposition: &Proposition) -> bool {
        let mut variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut variables);
        let mut candidates = variables
            .into_iter()
            .filter_map(|variable| {
                self.finite_context_range(variable)
                    .map(|range| (variable, range))
            })
            .filter(|(_, range)| range.lower <= range.upper)
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(_, range)| range.upper - range.lower);

        let Some((variable, range)) = candidates.into_iter().next() else {
            return false;
        };
        let Ok(width) = usize::try_from(range.upper - range.lower + 1) else {
            return false;
        };
        if width > FINITE_CONTEXT_SPLIT_LIMIT {
            return false;
        }

        let instances = (range.lower..=range.upper)
            .map(|value| {
                substitute_bitvector_variable_in_proposition(
                    proposition,
                    variable,
                    &signed_i64_bitvector_constant(value),
                )
            })
            .collect::<Vec<_>>();
        if instances
            .iter()
            .all(|instantiated| instantiated == proposition)
        {
            return false;
        }

        instances
            .iter()
            .all(|instantiated| self.proves(instantiated))
    }

    fn finite_context_range(&self, variable: Variable) -> Option<FiniteForAllRange> {
        let mut range = IntegerRangeFacts::default();
        for (condition, value) in &self.condition_facts {
            let Some((left, right, strict)) = condition_as_order_fact(condition, *value) else {
                continue;
            };
            match (bitvector_variable(&left), signed_bitvector_constant(&right)) {
                (Some(fact_variable), Some(bound)) if fact_variable == variable => {
                    let upper = if strict { bound.checked_sub(1)? } else { bound };
                    range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
                }
                _ => {}
            }
            match (signed_bitvector_constant(&left), bitvector_variable(&right)) {
                (Some(bound), Some(fact_variable)) if fact_variable == variable => {
                    let lower = if strict { bound.checked_add(1)? } else { bound };
                    range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
                }
                _ => {}
            }
        }

        let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
            return None;
        };
        Some(FiniteForAllRange { lower, upper })
    }

    fn proves_condition_from_facts(&self, condition: &ConditionTerm, value: bool) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact_condition, fact_value)| {
                fact_value == &value && self.condition_matches(fact_condition, condition)
            })
            || self
                .prop_facts
                .iter()
                .any(|proposition| self.proposition_proves_condition(proposition, condition, value))
            || self.proves_condition_from_derived_order_facts(condition, value)
    }

    fn proves_condition_from_derived_order_facts(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        let Some((left, right, strict)) = condition_as_order_fact(condition, value) else {
            return false;
        };
        let mut order_facts = self.condition_order_facts();
        self.collect_derived_order_facts(&mut order_facts);
        self.has_order_path_in_facts(&left, &right, strict, &order_facts)
    }

    fn proposition_proves_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        match proposition {
            Proposition::ConditionIs(fact_condition, fact_value) => {
                fact_value == &value && self.condition_matches(fact_condition, condition)
            }
            Proposition::And(left, right) => {
                self.proposition_proves_condition(left, condition, value)
                    || self.proposition_proves_condition(right, condition, value)
            }
            Proposition::Implies(left, right) => {
                self.proves_without_prop_facts(left)
                    && self.proposition_proves_condition(right, condition, value)
            }
            Proposition::ForAll { body, .. } => {
                self.proposition_proves_condition(body, condition, value)
                    || self
                        .forall_instantiations_for_condition(proposition, condition)
                        .iter()
                        .any(|body| self.proposition_proves_condition(body, condition, value))
            }
            _ => false,
        }
    }

    fn forall_instantiations_for_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
    ) -> Vec<Proposition> {
        let Proposition::ForAll { var, body, .. } = proposition else {
            return Vec::new();
        };
        let mut variables = BTreeSet::new();
        collect_condition_bitvector_variables(condition, &mut variables);
        variables
            .into_iter()
            .filter(|candidate| candidate != var)
            .map(|candidate| {
                substitute_bitvector_variable_in_proposition(
                    body,
                    *var,
                    &Bitvector32Term::Variable(candidate),
                )
            })
            .collect()
    }

    fn condition_matches(&self, fact: &ConditionTerm, target: &ConditionTerm) -> bool {
        if fact == target {
            return true;
        }

        match (fact, target) {
            (
                ConditionTerm::Bitvector32Equal(fact_left, fact_right),
                ConditionTerm::Bitvector32Equal(target_left, target_right),
            ) => {
                let fact_left = fact_left.as_ref();
                let fact_right = fact_right.as_ref();
                let target_left = target_left.as_ref();
                let target_right = target_right.as_ref();
                fact_right == target_right
                    && self.bitvector_terms_proven_equal(fact_left, target_left)
                    || fact_right == target_left
                        && self.bitvector_terms_proven_equal(fact_left, target_right)
                    || fact_left == target_right
                        && self.bitvector_terms_proven_equal(fact_right, target_left)
                    || fact_left == target_left
                        && self.bitvector_terms_proven_equal(fact_right, target_right)
            }
            (
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterEqual(target_left, target_right),
            ) => {
                self.bitvector_terms_proven_equal(fact_left, target_left)
                    && self.bitvector_terms_proven_equal(fact_right, target_right)
            }
            (
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterEqual(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            ) => {
                self.bitvector_terms_proven_equal(fact_left, target_right)
                    && self.bitvector_terms_proven_equal(fact_right, target_left)
            }
            _ => false,
        }
    }

    fn bitvector_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right
            || self.bitvector_if_terms_proven_equal(left, right)
            || self.bitvector_add_terms_proven_equal(left, right)
            || self.count_fold_split_terms_proven_equal(left, right)
            || self.memory_loads_proven_equal(left, right)
    }

    fn bitvector_if_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let (
            Bitvector32Term::If {
                condition: left_condition,
                then_term: left_then,
                else_term: left_else,
            },
            Bitvector32Term::If {
                condition: right_condition,
                then_term: right_then,
                else_term: right_else,
            },
        ) = (left, right)
        else {
            return false;
        };

        (left_condition == right_condition
            || self.condition_matches(left_condition, right_condition)
            || self.condition_matches(right_condition, left_condition))
            && self.bitvector_terms_proven_equal(left_then, right_then)
            && self.bitvector_terms_proven_equal(left_else, right_else)
    }

    fn bitvector_add_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if !matches!(left, Bitvector32Term::Add(_, _))
            && !matches!(right, Bitvector32Term::Add(_, _))
        {
            return false;
        }

        let mut left_terms = Vec::new();
        let mut left_constant = 0u32;
        collect_bitvector_add_terms(left, &mut left_terms, &mut left_constant);

        let mut right_terms = Vec::new();
        let mut right_constant = 0u32;
        collect_bitvector_add_terms(right, &mut right_terms, &mut right_constant);

        if left_constant != right_constant || left_terms.len() != right_terms.len() {
            return false;
        }

        for left_term in left_terms {
            let Some(index) = right_terms.iter().position(|right_term| {
                self.bitvector_addend_terms_proven_equal(&left_term, right_term)
            }) else {
                return false;
            };
            right_terms.remove(index);
        }

        right_terms.is_empty()
    }

    fn bitvector_addend_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right
            || self.bitvector_if_terms_proven_equal(left, right)
            || self.bitvector_terms_equal_from_facts(left, right)
            || self.memory_loads_proven_equal(left, right)
    }

    fn count_fold_split_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        count_fold_split_matches(left, right, self) || count_fold_split_matches(right, left, self)
    }

    fn proves_without_prop_facts(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) || self.is_inconsistent() {
            return true;
        }

        match proposition {
            Proposition::ConditionIs(condition, value) => self.decide(condition) == Some(*value),
            Proposition::And(left, right) => {
                self.proves_without_prop_facts(left) && self.proves_without_prop_facts(right)
            }
            Proposition::Or(left, right) => {
                self.proves_without_prop_facts(left) || self.proves_without_prop_facts(right)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide(condition) == Some(!*value)
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn is_inconsistent(&self) -> bool {
        let mut order_facts = Vec::new();
        let mut equal_facts = Vec::new();
        let mut disequal_facts = Vec::new();
        for (condition, value) in &self.condition_facts {
            match (condition, value) {
                (ConditionTerm::Constant(actual), expected) if actual != expected => return true,
                (ConditionTerm::Bitvector32Equal(left, right), true) => {
                    equal_facts.push((left.as_ref().clone(), right.as_ref().clone()));
                }
                (ConditionTerm::Bitvector32Equal(left, right), false) => {
                    disequal_facts.push((left.as_ref().clone(), right.as_ref().clone()));
                }
                _ => {
                    if let Some(order_fact) = condition_as_order_fact(condition, *value) {
                        order_facts.push(order_fact);
                    }
                }
            }
        }

        let condition_facts = self.condition_facts.iter().collect::<Vec<_>>();
        for left_index in 0..condition_facts.len() {
            for right_index in left_index + 1..condition_facts.len() {
                let ((left_condition, left_value), (right_condition, right_value)) =
                    (condition_facts[left_index], condition_facts[right_index]);
                if left_value != right_value
                    && self.condition_matches(left_condition, right_condition)
                {
                    return true;
                }
            }
        }

        for (equal_left, equal_right) in &equal_facts {
            if disequal_facts
                .iter()
                .any(|(disequal_left, disequal_right)| {
                    (equal_left == disequal_left && equal_right == disequal_right)
                        || (equal_left == disequal_right && equal_right == disequal_left)
                })
            {
                return true;
            }
        }

        for (left, right, strict) in &order_facts {
            if *strict && self.bitvector_terms_proven_equal(left, right) {
                return true;
            }
            if equal_facts.iter().any(|(equal_left, equal_right)| {
                (self.bitvector_terms_proven_equal(left, equal_left)
                    && self.bitvector_terms_proven_equal(right, equal_right))
                    || (self.bitvector_terms_proven_equal(left, equal_right)
                        && self.bitvector_terms_proven_equal(right, equal_left))
            }) && *strict
            {
                return true;
            }
            if order_facts
                .iter()
                .any(|(other_left, other_right, other_strict)| {
                    self.bitvector_terms_proven_equal(left, other_right)
                        && self.bitvector_terms_proven_equal(right, other_left)
                        && (*strict || *other_strict)
                })
            {
                return true;
            }
        }

        if finite_integer_range_exhausted(&order_facts, &equal_facts, &disequal_facts) {
            return true;
        }

        false
    }

    fn proves_not(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => self.decide(condition) == Some(!*value),
            Proposition::Not(body) => self.proves(body),
            _ => self
                .prop_facts
                .contains(&Proposition::Not(Box::new(proposition.clone()))),
        }
    }

    fn proves_memory_access(&self, memory: &CMemory, pointer: &Pointer, byte_width: u32) -> bool {
        if memory.access_in_bounds(pointer, byte_width) {
            return true;
        }
        if self.proves_access_from_memory_block(memory, pointer, byte_width) {
            return true;
        }

        self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryValidRange {
                memory: range_memory,
                base,
                bytes,
            } = proposition
            else {
                return false;
            };

            memory_range_still_available(range_memory, memory, base)
                && self.proves_access_from_valid_range(base, bytes, pointer, byte_width)
        })
    }

    fn proves_access_from_memory_block(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        let Some(block) = memory.blocks.get(&pointer.block) else {
            return false;
        };
        let base = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        self.proves_access_from_valid_range(
            &base,
            &Bitvector32Term::Constant(block.size()),
            pointer,
            byte_width,
        )
    }

    fn proves_access_from_valid_range(
        &self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        if byte_width != 4 || base.block != pointer.block {
            return false;
        }

        let Some(index) = pointer.element_index_from_base(base) else {
            return false;
        };
        let Some(element_count) = int32_element_count_from_bytes(bytes) else {
            return false;
        };

        self.decide(&ConditionTerm::signed_greater_equal(
            index.clone(),
            Bitvector32Term::Constant(0),
        )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(index, element_count)) == Some(true)
    }

    fn pointers_proven_disjoint_by_range(&self, left: &Pointer, right: &Pointer) -> bool {
        self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } = proposition
            else {
                return false;
            };

            self.pointer_in_range(left, left_base, left_start, left_end)
                && self.pointer_in_range(right, right_base, right_start, right_end)
                || self.pointer_in_range(right, left_base, left_start, left_end)
                    && self.pointer_in_range(left, right_base, right_start, right_end)
        })
    }

    fn pointer_in_range(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        let Some(index) = pointer.element_index_from_base(base) else {
            return false;
        };
        self.decide(&ConditionTerm::signed_less_equal(
            start.clone(),
            index.clone(),
        )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(index, end.clone())) == Some(true)
    }

    fn ranges_proven_disjoint_from_pointer(
        &self,
        ranges: &[CMemoryRange],
        pointer: &Pointer,
    ) -> bool {
        ranges
            .iter()
            .all(|range| self.range_proven_disjoint_from_pointer(range, pointer))
    }

    fn range_proven_disjoint_from_pointer(&self, range: &CMemoryRange, pointer: &Pointer) -> bool {
        if range.base.block != pointer.block {
            return true;
        }

        if let Some(index) = pointer.element_index_from_base(&range.base) {
            if self.decide(&ConditionTerm::signed_less_than(
                index.clone(),
                range.start.clone(),
            )) == Some(true)
                || self.decide(&ConditionTerm::signed_less_equal(range.end.clone(), index))
                    == Some(true)
            {
                return true;
            }
        }

        self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } = proposition
            else {
                return false;
            };

            self.range_covered_by_fact_range(range, left_base, left_start, left_end)
                && self.pointer_in_range(pointer, right_base, right_start, right_end)
                || self.range_covered_by_fact_range(range, right_base, right_start, right_end)
                    && self.pointer_in_range(pointer, left_base, left_start, left_end)
        })
    }

    fn range_covered_by_fact_range(
        &self,
        range: &CMemoryRange,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        let Some(base_delta) = range.base.element_index_from_base(base) else {
            return false;
        };
        let range_start = Bitvector32Term::add(base_delta.clone(), range.start.clone());
        let range_end = Bitvector32Term::add(base_delta, range.end.clone());

        self.decide(&ConditionTerm::signed_less_equal(
            start.clone(),
            range_start,
        )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_equal(range_end, end.clone())) == Some(true)
    }
}

impl ProofObligation {
    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            context: None,
            assumable: true,
        }
    }

    pub fn verification_condition(proposition: Proposition) -> Self {
        Self {
            proposition,
            context: None,
            assumable: false,
        }
    }

    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    pub fn is_assumable(&self) -> bool {
        self.assumable
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::ConditionIs(condition, value))
    }

    pub fn memory_can_load(memory: CMemory, pointer: Pointer) -> Self {
        Self::new(Proposition::CMemoryCanLoad { memory, pointer })
    }

    pub fn memory_can_store(memory: CMemory, pointer: Pointer) -> Self {
        Self::new(Proposition::CMemoryCanStore { memory, pointer })
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }

    fn map_proposition(self, f: impl FnOnce(Proposition) -> Proposition) -> Self {
        Self {
            proposition: f(self.proposition),
            context: self.context,
            assumable: self.assumable,
        }
    }
}

impl PathFact {
    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: true,
        }
    }

    fn internal(proposition: Proposition) -> Self {
        Self {
            proposition,
            public: false,
        }
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::ConditionIs(condition, value))
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    fn is_public(&self) -> bool {
        self.public
    }
}

impl SymbolicCExecution {
    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicCExecutionPath {
    pub fn facts(&self) -> &[PathFact] {
        &self.facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

pub fn int32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int32(bits.into())
}

pub fn c_variable(name: impl Into<String>) -> CExpression {
    CExpression::Variable(name.into())
}

pub fn c_addr_of(name: impl Into<String>) -> CExpression {
    CExpression::AddressOf(Box::new(c_variable(name)))
}

pub fn c_int32_literal(value: u32) -> CExpression {
    CExpression::Value(int32(Bitvector32Term::Constant(value)))
}

pub fn c_pointer_value(pointer: Pointer) -> CExpression {
    CExpression::Value(CValue::Pointer(pointer))
}

pub fn c_less_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessThan(Box::new(left), Box::new(right))
}

pub fn c_less_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessEqual(Box::new(left), Box::new(right))
}

pub fn c_greater_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterThan(Box::new(left), Box::new(right))
}

pub fn c_greater_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterEqual(Box::new(left), Box::new(right))
}

pub fn c_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Equal(Box::new(left), Box::new(right))
}

pub fn c_not_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::NotEqual(Box::new(left), Box::new(right))
}

pub fn c_not(expression: CExpression) -> CExpression {
    CExpression::Not(Box::new(expression))
}

pub fn c_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::And(Box::new(left), Box::new(right))
}

pub fn c_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Or(Box::new(left), Box::new(right))
}

pub fn c_add(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Add(Box::new(left), Box::new(right))
}

pub fn c_subtract(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Subtract(Box::new(left), Box::new(right))
}

pub fn c_load(pointer: CExpression) -> CExpression {
    CExpression::Load(Box::new(pointer))
}

pub fn c_index(base: CExpression, index: CExpression) -> CExpression {
    CExpression::Index(Box::new(base), Box::new(index))
}

pub fn c_assign(name: impl Into<String>, expression: CExpression) -> CStatement {
    CStatement::Assign {
        name: name.into(),
        expression,
    }
}

pub fn c_call_assign(
    target: impl Into<String>,
    function_name: impl Into<String>,
    arguments: Vec<CExpression>,
) -> CStatement {
    CStatement::CallAssign {
        target: target.into(),
        function_name: function_name.into(),
        arguments,
    }
}

pub fn c_declare(name: impl Into<String>, c_type: CType) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type,
    }
}

pub fn c_assert(condition: CExpression) -> CStatement {
    CStatement::Assert {
        condition,
        label: None,
    }
}

pub fn c_labeled_assert(condition: CExpression, label: impl Into<String>) -> CStatement {
    CStatement::Assert {
        condition,
        label: Some(label.into()),
    }
}

pub fn c_seq(first: CStatement, second: CStatement) -> CStatement {
    CStatement::Seq(Box::new(first), Box::new(second))
}

pub fn c_return(expression: CExpression) -> CStatement {
    CStatement::Return(expression)
}

pub fn c_store(pointer: CExpression, value: CExpression) -> CStatement {
    CStatement::Store { pointer, value }
}

pub fn c_if(
    condition: CExpression,
    then_branch: CStatement,
    else_branch: CStatement,
) -> CStatement {
    CStatement::If {
        condition,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn c_while(
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(condition, invariant, Vec::new(), Vec::new(), body)
}

pub fn c_while_with_invariant_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(
        condition,
        invariant,
        invariant_checks,
        Vec::new(),
        body,
    )
}

pub fn c_while_with_invariant_and_effect_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    effect_checks: Vec<CLoopEffectCheck>,
    body: CStatement,
) -> CStatement {
    CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body: Box::new(body),
    }
}

pub fn c_parameter(name: impl Into<String>, c_type: CType) -> CParameter {
    CParameter::new(name, c_type)
}

pub fn c_function(
    return_type: CType,
    name: impl Into<String>,
    parameters: Vec<CParameter>,
    body: CStatement,
) -> CFunction {
    CFunction::new(return_type, name, parameters, body)
}

pub fn c_function_specification(
    state: CState,
    arguments: Vec<CExpression>,
    requires: Vec<Proposition>,
    outcome: CFunctionOutcome,
) -> CFunctionSpecification {
    CFunctionSpecification::new(state, arguments, requires, outcome)
}

pub fn proposition_and(left: Proposition, right: Proposition) -> Proposition {
    Proposition::And(Box::new(left), Box::new(right))
}

pub fn proposition_and_all(mut propositions: Vec<Proposition>) -> Proposition {
    let Some(first) = propositions.pop() else {
        return Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    };

    propositions
        .into_iter()
        .rev()
        .fold(first, |right, left| proposition_and(left, right))
}

pub fn c_max_body() -> CStatement {
    c_if(
        c_less_than(c_variable("a"), c_variable("b")),
        c_return(c_variable("b")),
        c_return(c_variable("a")),
    )
}

pub fn c_max_function() -> CFunction {
    c_function(
        CType::Int32,
        "max",
        vec![
            c_parameter("a", CType::Int32),
            c_parameter("b", CType::Int32),
        ],
        c_max_body(),
    )
}

pub fn c_max_environment(a: CValue, b: CValue) -> CLocalEnvironment {
    CLocalEnvironment::new().with("a", a).with("b", b)
}

pub fn c_max_state(a: CValue, b: CValue) -> CState {
    CState::new().with_local("a", a).with_local("b", b)
}

pub fn c_max_lt_condition(a: Bitvector32Term, b: Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_than(a, b)
}

pub fn prove_c_expression_evaluation(state: CState, expression: CExpression) -> Option<Theorem> {
    let outcome = evaluate_c_expression(
        &state,
        &expression,
        &Assumptions::new(),
        &mut ExecutionBudget::default(),
    )?;
    Some(Theorem::new(Proposition::CExpressionEvaluates {
        state,
        expression,
        outcome,
    }))
}

pub fn prove_c_statement_execution(state: CState, statement: CStatement) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, Assumptions::new())
}

pub fn prove_c_statement_execution_under_assumptions(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, assumptions)
}

pub fn prove_symbolic_c_execution(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_budget(
        state,
        statement,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CFunctionEnvironment::new(),
        budget,
    )
}

pub fn prove_symbolic_c_execution_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_execution_paths(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_budget(
        state,
        statement,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_paths_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CFunctionEnvironment::new(),
        budget,
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
    mut budget: ExecutionBudget,
) -> SymbolicCExecution {
    let paths = match execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        &mut budget,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let facts = public_path_facts(&path.facts);
            let proposition = Proposition::CStatementExecutes {
                state: state.clone(),
                statement: statement.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_function_execution(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CFunctionEnvironment::new(),
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_function_execution_paths(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CFunctionEnvironment::new(),
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
    mut budget: ExecutionBudget,
) -> SymbolicCExecution {
    let paths = match execute_c_function_paths(
        &state,
        &function,
        &arguments,
        &assumptions,
        &environment,
        &mut budget,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let facts = public_path_facts(&path.facts);
            let proposition = Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments: arguments.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_function_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_verification_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
    mut budget: ExecutionBudget,
) -> SymbolicCExecution {
    let mut variables = VerificationVariableGenerator::new(1_000_000);
    let paths = match execute_c_function_verification_paths(
        &state,
        &function,
        &arguments,
        &assumptions,
        &environment,
        &mut budget,
        &mut variables,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let facts = public_path_facts(&path.facts);
            let proposition = Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments: arguments.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_c_function_satisfies_specification_from_symbolic_path(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
    facts: &[PathFact],
    obligations: &[ProofObligation],
) -> Theorem {
    let requires = specification.requires().to_vec();
    let proposition = requires.iter().rev().fold(
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        },
        |body, requirement| Proposition::Implies(Box::new(requirement.clone()), Box::new(body)),
    );
    Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        facts,
        obligations,
    ))
}

pub fn prove_c_function_satisfies_specification(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification_with_environment(
        function,
        specification,
        assumptions,
        CFunctionEnvironment::new(),
    )
}

pub fn prove_c_function_satisfies_specification_with_environment(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
    environment: CFunctionEnvironment,
) -> Option<Theorem> {
    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    let paths = execute_c_function_paths(
        specification.state(),
        &function,
        specification.arguments(),
        &specification_assumptions,
        &environment,
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some()
        || path.facts.iter().any(PathFact::is_public)
        || !path.obligations.is_empty()
        || &path.outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let proposition = requires.iter().rev().fold(
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        },
        |body, requirement| Proposition::Implies(Box::new(requirement.clone()), Box::new(body)),
    );
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_function_satisfies_specification_and_propositions(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
    propositions: Vec<Proposition>,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        assumptions.clone(),
    )?;

    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    if propositions
        .iter()
        .any(|proposition| !specification_assumptions.proves(proposition))
    {
        return None;
    }

    let conclusion = proposition_and_all(
        std::iter::once(Proposition::CFunctionSatisfiesSpecification {
            function: function.clone(),
            specification: specification.clone(),
        })
        .chain(propositions)
        .collect(),
    );
    let proposition = specification
        .requires()
        .iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
        });
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_statement_executes_and_propositions(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    propositions: Vec<Proposition>,
) -> Option<Theorem> {
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &CFunctionEnvironment::new(),
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.facts.is_empty() || !path.obligations.is_empty() {
        return None;
    }
    if propositions
        .iter()
        .any(|proposition| !assumptions.proves(proposition))
    {
        return None;
    }
    let conclusion = proposition_and_all(
        std::iter::once(Proposition::CStatementExecutes {
            state,
            statement,
            outcome: path.outcome,
        })
        .chain(propositions)
        .collect(),
    );
    Some(Theorem::new(wrap_proof_facts(
        conclusion,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_max_lt_returns_right(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(a_value, b_value.clone());
    let assumptions = Assumptions::new().assume_condition(condition.clone(), true);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: b_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, true)),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_c_max_not_lt_returns_left(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits, b_bits);
    let state = c_max_state(a_value.clone(), b_value);
    let assumptions = Assumptions::new().assume_condition(condition.clone(), false);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: a_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, false)),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_memory_load(memory: CMemory, pointer: Pointer) -> Theorem {
    let outcome = memory.load(&pointer);
    Theorem::new(Proposition::CMemoryLoads {
        memory,
        pointer,
        outcome,
    })
}

pub fn prove_memory_load_after_store_same(
    memory: CMemory,
    pointer: Pointer,
    value: CValue,
) -> Theorem {
    let stored = memory.store(pointer.clone(), value.clone());
    Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer,
        outcome: CExpressionOutcome::Value(value),
    })
}

pub fn prove_memory_load_after_store_other(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
) -> Option<Theorem> {
    if stored_pointer == loaded_pointer {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer: loaded_pointer,
        outcome,
    }))
}

pub fn prove_memory_load_after_store_distinct_under_assumptions(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
    assumptions: Assumptions,
) -> Option<Theorem> {
    if !pointers_proven_distinct(&stored_pointer, &loaded_pointer, &assumptions) {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(wrap_proof_facts(
        Proposition::CMemoryLoads {
            memory: stored,
            pointer: loaded_pointer,
            outcome,
        },
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_while_invariant_rule(
    state: CState,
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
    assumptions: Assumptions,
    preserved: Vec<Proposition>,
    postcondition: Proposition,
) -> Option<Theorem> {
    if invariant
        .iter()
        .any(|invariant| !assumptions.proves(invariant))
    {
        return None;
    }

    let loop_assumptions = assumptions_with_propositions(&assumptions, &invariant);
    let step_ok = condition_contexts_for_truthiness(&state, &condition, &loop_assumptions, true)
        .into_iter()
        .any(|step_assumptions| {
            let body_paths = execute_c_statement_paths(
                &state,
                &body,
                &step_assumptions,
                &CFunctionEnvironment::new(),
                &mut ExecutionBudget::default(),
            );
            let Ok(body_paths) = body_paths else {
                return false;
            };
            let mut body_paths = body_paths.into_iter();
            let Some(body_path) = body_paths.next() else {
                return false;
            };
            if body_paths.next().is_some()
                || !body_path.facts.is_empty()
                || !body_path.obligations.is_empty()
                || !matches!(body_path.outcome, CStatementOutcome::Normal(_))
            {
                return false;
            }
            preserved
                .iter()
                .all(|preserved| step_assumptions.proves(preserved))
        });

    if !step_ok {
        return None;
    }

    let exit_ok = condition_contexts_for_truthiness(&state, &condition, &loop_assumptions, false)
        .into_iter()
        .any(|exit_assumptions| exit_assumptions.proves(&postcondition));

    if !exit_ok {
        return None;
    }

    Some(Theorem::new(wrap_proof_facts(
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition: Box::new(postcondition),
        },
        &assumptions,
        &[],
        &[],
    )))
}

fn condition_contexts_for_truthiness(
    state: &CState,
    condition: &CExpression,
    assumptions: &Assumptions,
    desired_truthiness: bool,
) -> Vec<Assumptions> {
    let mut contexts = Vec::new();
    let Ok(condition_paths) = evaluate_c_expression_paths(
        state,
        condition,
        assumptions,
        &mut ExecutionBudget::default(),
    ) else {
        return contexts;
    };
    for condition_path in condition_paths {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        let CExpressionOutcome::Value(value) = outcome else {
            continue;
        };

        for truthiness_path in
            c_truthiness_paths(value, facts.clone(), obligations.clone(), assumptions)
        {
            if truthiness_path.is_true == desired_truthiness {
                contexts.push(assumptions_with_path_context(
                    assumptions,
                    &truthiness_path.facts,
                    &truthiness_path.obligations,
                ));
            }
        }
    }
    contexts
}

fn pointers_proven_distinct(left: &Pointer, right: &Pointer, assumptions: &Assumptions) -> bool {
    left.block != right.block
        || assumptions.decide(&ConditionTerm::pointer_offset_equal(
            left.offset.clone(),
            right.offset.clone(),
        )) == Some(false)
        || assumptions.pointers_proven_disjoint_by_range(left, right)
}

fn pointers_proven_equal(left: &Pointer, right: &Pointer, assumptions: &Assumptions) -> bool {
    left == right
        || left.block == right.block
            && assumptions.decide(&ConditionTerm::pointer_offset_equal(
                left.offset.clone(),
                right.offset.clone(),
            )) == Some(true)
}

fn memories_match_for_pointer_load(left: &CMemory, right: &CMemory, pointer: &Pointer) -> bool {
    if left == right {
        return true;
    }
    if pointer.block.starts_with("local:") {
        return false;
    }

    left.blocks
        .iter()
        .filter(|(block, _)| !block.starts_with("local:"))
        .eq(right
            .blocks
            .iter()
            .filter(|(block, _)| !block.starts_with("local:")))
        && left
            .cells
            .iter()
            .filter(|(cell_pointer, _)| cell_pointer.block == pointer.block)
            .eq(right
                .cells
                .iter()
                .filter(|(cell_pointer, _)| cell_pointer.block == pointer.block))
}

fn memories_match_for_pointer_load_under_assumptions(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    if pointer.block.starts_with("local:") {
        return false;
    }
    if !left
        .blocks
        .iter()
        .filter(|(block, _)| !block.starts_with("local:"))
        .eq(right
            .blocks
            .iter()
            .filter(|(block, _)| !block.starts_with("local:")))
    {
        return false;
    }

    left.differing_cell_pointers(right)
        .into_iter()
        .filter(|cell_pointer| !cell_pointer.block.starts_with("local:"))
        .all(|cell_pointer| pointers_proven_distinct(&cell_pointer, pointer, assumptions))
}

fn memory_matches_effect_summary_endpoint(
    expected: &CMemory,
    actual: &CMemory,
    pointer: &Pointer,
) -> bool {
    expected == actual || memories_match_for_pointer_load(expected, actual, pointer)
}

fn condition_as_order_fact(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), true))
        }
        _ => None,
    }
}

const FINITE_FORALL_INSTANTIATION_LIMIT: usize = 128;
const FINITE_CONTEXT_SPLIT_LIMIT: usize = 8;
const DISJUNCTION_CASE_LIMIT: usize = 8;

#[derive(Clone, Debug, Default)]
struct FiniteForAllRange {
    lower: i64,
    upper: i64,
}

#[derive(Clone, Debug)]
struct VariableOrderEdge {
    lower: Variable,
    upper: Variable,
    strict: bool,
}

fn collect_forall_chain<'a>(
    proposition: &'a Proposition,
    variables: &mut Vec<Variable>,
) -> &'a Proposition {
    match proposition {
        Proposition::ForAll {
            var,
            sort: Sort::CInt32,
            body,
        } => {
            variables.push(*var);
            collect_forall_chain(body, variables)
        }
        proposition => proposition,
    }
}

fn collect_or_cases(proposition: &Proposition, cases: &mut Vec<Proposition>) {
    match proposition {
        Proposition::Or(left, right) => {
            collect_or_cases(left, cases);
            collect_or_cases(right, cases);
        }
        proposition => cases.push(proposition.clone()),
    }
}

fn finite_forall_ranges(
    variables: &[Variable],
    body: &Proposition,
) -> Option<Vec<FiniteForAllRange>> {
    let variable_set = variables.iter().copied().collect::<BTreeSet<_>>();
    let mut ranges = variables
        .iter()
        .copied()
        .map(|variable| (variable, IntegerRangeFacts::default()))
        .collect::<BTreeMap<_, _>>();
    let mut edges = Vec::new();
    let mut order_facts = Vec::new();
    collect_implication_antecedent_order_facts(body, &mut order_facts);

    for (left, right, strict) in order_facts {
        match (bitvector_variable(&left), signed_bitvector_constant(&right)) {
            (Some(variable), Some(bound)) if variable_set.contains(&variable) => {
                let upper = if strict { bound.checked_sub(1)? } else { bound };
                tighten_upper_bound(&mut ranges, variable, upper);
                continue;
            }
            _ => {}
        }
        match (signed_bitvector_constant(&left), bitvector_variable(&right)) {
            (Some(bound), Some(variable)) if variable_set.contains(&variable) => {
                let lower = if strict { bound.checked_add(1)? } else { bound };
                tighten_lower_bound(&mut ranges, variable, lower);
                continue;
            }
            _ => {}
        }
        match (bitvector_variable(&left), bitvector_variable(&right)) {
            (Some(lower), Some(upper))
                if variable_set.contains(&lower) && variable_set.contains(&upper) =>
            {
                edges.push(VariableOrderEdge {
                    lower,
                    upper,
                    strict,
                });
            }
            _ => {}
        }
    }

    propagate_variable_order_bounds(&mut ranges, &edges)?;

    variables
        .iter()
        .map(|variable| {
            let range = ranges.get(variable)?;
            let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
                return None;
            };
            if lower > upper || upper - lower > 32 {
                return None;
            }
            Some(FiniteForAllRange { lower, upper })
        })
        .collect()
}

fn collect_implication_antecedent_order_facts(
    proposition: &Proposition,
    facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
) {
    match proposition {
        Proposition::Implies(left, _) => collect_order_facts_from_assumed_proposition(left, facts),
        Proposition::And(left, right) | Proposition::Or(left, right) => {
            collect_implication_antecedent_order_facts(left, facts);
            collect_implication_antecedent_order_facts(right, facts);
        }
        Proposition::ForAll { body, .. } => collect_implication_antecedent_order_facts(body, facts),
        Proposition::Not(_)
        | Proposition::ConditionIs(_, _)
        | Proposition::Equal(_, _)
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
        | Proposition::CWhileInvariantRule { .. } => {}
    }
}

fn collect_order_facts_from_assumed_proposition(
    proposition: &Proposition,
    facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
) {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            if let Some(fact) = condition_as_order_fact(condition, *value) {
                facts.push(fact);
            }
        }
        Proposition::And(left, right) => {
            collect_order_facts_from_assumed_proposition(left, facts);
            collect_order_facts_from_assumed_proposition(right, facts);
        }
        _ => {}
    }
}

fn tighten_lower_bound(
    ranges: &mut BTreeMap<Variable, IntegerRangeFacts>,
    variable: Variable,
    lower: i64,
) {
    if let Some(range) = ranges.get_mut(&variable) {
        range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
    }
}

fn tighten_upper_bound(
    ranges: &mut BTreeMap<Variable, IntegerRangeFacts>,
    variable: Variable,
    upper: i64,
) {
    if let Some(range) = ranges.get_mut(&variable) {
        range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
    }
}

fn propagate_variable_order_bounds(
    ranges: &mut BTreeMap<Variable, IntegerRangeFacts>,
    edges: &[VariableOrderEdge],
) -> Option<()> {
    let mut changed = true;
    while changed {
        changed = false;
        for edge in edges {
            let lower_range = ranges.get(&edge.lower)?;
            let upper_range = ranges.get(&edge.upper)?;
            let offset = if edge.strict { 1 } else { 0 };
            let inferred_lower_upper = upper_range
                .upper
                .and_then(|upper| upper.checked_sub(offset));
            let inferred_upper_lower = lower_range
                .lower
                .and_then(|lower| lower.checked_add(offset));

            if let Some(upper) = inferred_lower_upper {
                let range = ranges.get_mut(&edge.lower)?;
                let new_upper = range.upper.map_or(upper, |current| current.min(upper));
                if range.upper != Some(new_upper) {
                    range.upper = Some(new_upper);
                    changed = true;
                }
            }

            if let Some(lower) = inferred_upper_lower {
                let range = ranges.get_mut(&edge.upper)?;
                let new_lower = range.lower.map_or(lower, |current| current.max(lower));
                if range.lower != Some(new_lower) {
                    range.lower = Some(new_lower);
                    changed = true;
                }
            }
        }
    }
    Some(())
}

fn signed_i64_bitvector_constant(value: i64) -> Bitvector32Term {
    debug_assert!((i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&value));
    Bitvector32Term::Constant(value as i32 as u32)
}

fn instantiate_range_fold_step(
    body: &Bitvector32Term,
    accumulator: Variable,
    accumulator_value: &Bitvector32Term,
    item: Variable,
    item_value: &Bitvector32Term,
) -> Bitvector32Term {
    let body = substitute_bitvector_variable(body, accumulator, accumulator_value);
    substitute_bitvector_variable(&body, item, item_value)
}

#[derive(Clone, Debug, Default)]
struct IntegerRangeFacts {
    lower: Option<i64>,
    upper: Option<i64>,
    excluded: BTreeSet<i64>,
}

fn finite_integer_range_exhausted(
    order_facts: &[(Bitvector32Term, Bitvector32Term, bool)],
    equal_facts: &[(Bitvector32Term, Bitvector32Term)],
    disequal_facts: &[(Bitvector32Term, Bitvector32Term)],
) -> bool {
    let mut ranges: BTreeMap<Variable, IntegerRangeFacts> = BTreeMap::new();

    for (left, right, strict) in order_facts {
        match (bitvector_variable(left), signed_bitvector_constant(right)) {
            (Some(variable), Some(bound)) => {
                let upper = if *strict { bound - 1 } else { bound };
                let range = ranges.entry(variable).or_default();
                range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
            }
            _ => {}
        }
        match (signed_bitvector_constant(left), bitvector_variable(right)) {
            (Some(bound), Some(variable)) => {
                let lower = if *strict { bound + 1 } else { bound };
                let range = ranges.entry(variable).or_default();
                range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
            }
            _ => {}
        }
    }

    for (left, right) in equal_facts {
        if let Some((variable, value)) = bitvector_variable_and_constant(left, right) {
            let range = ranges.entry(variable).or_default();
            range.lower = Some(range.lower.map_or(value, |current| current.max(value)));
            range.upper = Some(range.upper.map_or(value, |current| current.min(value)));
        }
    }

    for (left, right) in disequal_facts {
        if let Some((variable, value)) = bitvector_variable_and_constant(left, right) {
            ranges.entry(variable).or_default().excluded.insert(value);
        }
    }

    ranges.into_values().any(|range| {
        let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
            return false;
        };
        if lower > upper {
            return true;
        }
        upper - lower <= 256 && (lower..=upper).all(|value| range.excluded.contains(&value))
    })
}

fn bitvector_variable(term: &Bitvector32Term) -> Option<Variable> {
    match term {
        Bitvector32Term::Variable(variable) => Some(*variable),
        _ => None,
    }
}

fn signed_bitvector_constant(term: &Bitvector32Term) -> Option<i64> {
    term.as_const().map(|value| i64::from(value as i32))
}

fn signed_u32_constant(value: u32) -> Option<i64> {
    i32::try_from(value).ok().map(i64::from)
}

fn bitvector_variable_and_constant(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(Variable, i64)> {
    bitvector_variable(left)
        .zip(signed_bitvector_constant(right))
        .or_else(|| bitvector_variable(right).zip(signed_bitvector_constant(left)))
}

fn bitvector_equality_after_additive_cancellation(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(Bitvector32Term, Bitvector32Term)> {
    match (left, right) {
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_base => {
            Some((left_addend.as_ref().clone(), right_addend.as_ref().clone()))
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_addend => {
            Some((left_addend.as_ref().clone(), right_base.as_ref().clone()))
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_base => {
            Some((left_base.as_ref().clone(), right_addend.as_ref().clone()))
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_addend => {
            Some((left_base.as_ref().clone(), right_base.as_ref().clone()))
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_base.as_ref() == right => {
            Some((left_addend.as_ref().clone(), Bitvector32Term::Constant(0)))
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_addend.as_ref() == right => {
            Some((left_base.as_ref().clone(), Bitvector32Term::Constant(0)))
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if left == right_base.as_ref() => {
            Some((Bitvector32Term::Constant(0), right_addend.as_ref().clone()))
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if left == right_addend.as_ref() => {
            Some((Bitvector32Term::Constant(0), right_base.as_ref().clone()))
        }
        _ => None,
    }
}

#[derive(Clone, Debug)]
struct CountFoldParts {
    start: Bitvector32Term,
    end: Bitvector32Term,
    accumulator: Variable,
    item: Variable,
    contribution: Bitvector32Term,
}

fn collect_bitvector_add_terms(
    term: &Bitvector32Term,
    terms: &mut Vec<Bitvector32Term>,
    constant: &mut u32,
) {
    match term {
        Bitvector32Term::Add(left, right) => {
            collect_bitvector_add_terms(left, terms, constant);
            collect_bitvector_add_terms(right, terms, constant);
        }
        Bitvector32Term::Constant(value) => {
            *constant = constant.wrapping_add(*value);
        }
        term => terms.push(term.clone()),
    }
}

fn count_fold_parts(term: &Bitvector32Term) -> Option<CountFoldParts> {
    let Bitvector32Term::RangeFold {
        start,
        end,
        initial,
        accumulator,
        item,
        body,
    } = term
    else {
        return None;
    };

    if initial.as_ref() != &Bitvector32Term::Constant(0) {
        return None;
    }

    let contribution = match body.as_ref() {
        Bitvector32Term::Add(left, right)
            if left.as_ref() == &Bitvector32Term::Variable(*accumulator) =>
        {
            right.as_ref().clone()
        }
        Bitvector32Term::Add(left, right)
            if right.as_ref() == &Bitvector32Term::Variable(*accumulator) =>
        {
            left.as_ref().clone()
        }
        _ => return None,
    };

    Some(CountFoldParts {
        start: start.as_ref().clone(),
        end: end.as_ref().clone(),
        accumulator: *accumulator,
        item: *item,
        contribution,
    })
}

fn count_fold_split_matches(
    whole: &Bitvector32Term,
    split: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    let Some(whole) = count_fold_parts(whole) else {
        return false;
    };
    let Bitvector32Term::Add(left, right) = split else {
        return false;
    };

    count_fold_split_parts_match(&whole, left.as_ref(), right.as_ref(), assumptions)
        || count_fold_split_parts_match(&whole, right.as_ref(), left.as_ref(), assumptions)
}

fn count_fold_split_parts_match(
    whole: &CountFoldParts,
    first: &Bitvector32Term,
    second: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    let (Some(first), Some(second)) = (count_fold_parts(first), count_fold_parts(second)) else {
        return false;
    };

    whole.accumulator == first.accumulator
        && whole.accumulator == second.accumulator
        && whole.item == first.item
        && whole.item == second.item
        && assumptions.bitvector_terms_proven_equal(&whole.contribution, &first.contribution)
        && assumptions.bitvector_terms_proven_equal(&whole.contribution, &second.contribution)
        && assumptions.bitvector_terms_proven_equal(&whole.start, &first.start)
        && assumptions.bitvector_terms_proven_equal(&first.end, &second.start)
        && assumptions.bitvector_terms_proven_equal(&whole.end, &second.end)
}

fn bitvector_same_base_nonzero_const_offset(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    if let Some((left_base, left_addend)) = left.add_const_parts() {
        if &left_base == right {
            return left_addend != 0;
        }
        if let Some((right_base, right_addend)) = right.add_const_parts() {
            return left_base == right_base && left_addend != right_addend;
        }
    }

    if let Some((right_base, right_addend)) = right.add_const_parts() {
        return &right_base == left && right_addend != 0;
    }

    false
}

fn collect_proposition_bitvector_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        Proposition::Equal(left, right) => {
            collect_term_bitvector_variables(left, variables);
            collect_term_bitvector_variables(right, variables);
        }
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bitvector_variables(condition, variables);
        }
        Proposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_term_bitvector_variables(argument, variables);
            }
        }
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_expression_bitvector_variables(expression, variables);
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_statement_bitvector_variables(statement, variables);
            collect_c_statement_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CFunctionExecutes {
            state,
            arguments,
            function,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
            collect_c_function_bitvector_variables(function, variables);
            collect_c_function_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => {
            collect_c_function_bitvector_variables(function, variables);
            collect_c_function_specification_bitvector_variables(specification, variables);
        }
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CMemoryCanLoad { memory, pointer }
        | Proposition::CMemoryCanStore { memory, pointer } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Proposition::CMemoryValidRange {
            memory,
            base,
            bytes,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(base, variables);
            collect_bitvector_variables(bytes, variables);
        }
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => {
            collect_pointer_bitvector_variables(left_base, variables);
            collect_bitvector_variables(left_start, variables);
            collect_bitvector_variables(left_end, variables);
            collect_pointer_bitvector_variables(right_base, variables);
            collect_bitvector_variables(right_start, variables);
            collect_bitvector_variables(right_end, variables);
        }
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for pointer in pointers {
                collect_pointer_bitvector_variables(pointer, variables);
            }
        }
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for range in mutable_ranges {
                collect_c_memory_range_bitvector_variables(range, variables);
            }
        }
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_expression_bitvector_variables(condition, variables);
            for proposition in invariant {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            collect_c_statement_bitvector_variables(body, variables);
            for proposition in preserved {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            collect_proposition_bitvector_variables(postcondition, variables);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bitvector_variables(left, variables);
            collect_proposition_bitvector_variables(right, variables);
        }
        Proposition::Not(body) => collect_proposition_bitvector_variables(body, variables),
        Proposition::ForAll { var, body, .. } => {
            collect_proposition_bitvector_variables(body, variables);
            variables.remove(var);
        }
    }
}

fn collect_term_bitvector_variables(term: &Term, variables: &mut BTreeSet<Variable>) {
    match term {
        Term::Condition(condition) => collect_condition_bitvector_variables(condition, variables),
        Term::Bitvector32(bits) => collect_bitvector_variables(bits, variables),
        Term::PointerOffset(offset) => {
            collect_pointer_offset_bitvector_variables(offset, variables)
        }
        Term::CValue(value) => collect_c_value_bitvector_variables(value, variables),
        Term::CExpressionOutcome(outcome) => {
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Term::CStatementOutcome(outcome) => {
            collect_c_statement_outcome_bitvector_variables(outcome, variables);
        }
        Term::CFunctionOutcome(outcome) => {
            collect_c_function_outcome_bitvector_variables(outcome, variables);
        }
        Term::CMemory(memory) => collect_memory_bitvector_variables(memory, variables),
        Term::CState(state) => collect_c_state_bitvector_variables(state, variables),
    }
}

fn collect_c_expression_bitvector_variables(
    expression: &CExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        CExpression::Value(value) => collect_c_value_bitvector_variables(value, variables),
        CExpression::Variable(_) => {}
        CExpression::AddressOf(body) | CExpression::Not(body) | CExpression::Load(body) => {
            collect_c_expression_bitvector_variables(body, variables);
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
        | CExpression::Index(left, right) => {
            collect_c_expression_bitvector_variables(left, variables);
            collect_c_expression_bitvector_variables(right, variables);
        }
    }
}

fn collect_c_statement_bitvector_variables(
    statement: &CStatement,
    variables: &mut BTreeSet<Variable>,
) {
    match statement {
        CStatement::Declare { .. } => {}
        CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Assert {
            condition: expression,
            ..
        } => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
        CStatement::CallAssign { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
        }
        CStatement::Seq(first, second) => {
            collect_c_statement_bitvector_variables(first, variables);
            collect_c_statement_bitvector_variables(second, variables);
        }
        CStatement::Store { pointer, value } => {
            collect_c_expression_bitvector_variables(pointer, variables);
            collect_c_expression_bitvector_variables(value, variables);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bitvector_variables(condition, variables);
            collect_c_statement_bitvector_variables(then_branch, variables);
            collect_c_statement_bitvector_variables(else_branch, variables);
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
        } => {
            collect_c_expression_bitvector_variables(condition, variables);
            for proposition in invariant {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            for check in invariant_checks {
                collect_c_proposition_bitvector_variables(check.proposition(), variables);
            }
            for check in effect_checks {
                collect_loop_effect_bitvector_variables(check.effect(), variables);
            }
            collect_c_statement_bitvector_variables(body, variables);
        }
    }
}

fn collect_c_proposition_bitvector_variables(
    proposition: &CProposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        CProposition::Comparison { left, right, .. } => {
            collect_c_expression_bitvector_variables(left, variables);
            collect_c_expression_bitvector_variables(right, variables);
        }
        CProposition::And(left, right)
        | CProposition::Or(left, right)
        | CProposition::Implies(left, right) => {
            collect_c_proposition_bitvector_variables(left, variables);
            collect_c_proposition_bitvector_variables(right, variables);
        }
        CProposition::Not(body) => collect_c_proposition_bitvector_variables(body, variables),
        CProposition::ForAllInt32 { variable, body, .. } => {
            collect_c_proposition_bitvector_variables(body, variables);
            variables.remove(variable);
        }
        CProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
        }
    }
}

fn collect_loop_effect_bitvector_variables(
    effect: &CLoopEffect,
    variables: &mut BTreeSet<Variable>,
) {
    match effect {
        CLoopEffect::Immutable => {}
        CLoopEffect::Mutable(segments) => {
            for segment in segments {
                collect_c_expression_bitvector_variables(&segment.base, variables);
                collect_c_expression_bitvector_variables(&segment.start, variables);
                collect_c_expression_bitvector_variables(&segment.end, variables);
            }
        }
    }
}

fn collect_c_expression_outcome_bitvector_variables(
    outcome: &CExpressionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    if let CExpressionOutcome::Value(value) = outcome {
        collect_c_value_bitvector_variables(value, variables);
    }
}

fn collect_c_statement_outcome_bitvector_variables(
    outcome: &CStatementOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CStatementOutcome::Normal(state) => collect_c_state_bitvector_variables(state, variables),
        CStatementOutcome::Return { value, state } => {
            collect_c_value_bitvector_variables(value, variables);
            collect_c_state_bitvector_variables(state, variables);
        }
        CStatementOutcome::UndefinedBehavior(_) | CStatementOutcome::RuntimeError(_) => {}
    }
}

fn collect_c_function_outcome_bitvector_variables(
    outcome: &CFunctionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CFunctionOutcome::Return { value, state } => {
            collect_c_value_bitvector_variables(value, variables);
            collect_c_state_bitvector_variables(state, variables);
        }
        CFunctionOutcome::UndefinedBehavior(_) | CFunctionOutcome::RuntimeError(_) => {}
    }
}

fn collect_c_state_bitvector_variables(state: &CState, variables: &mut BTreeSet<Variable>) {
    for binding in state.locals.bindings.values() {
        match binding {
            CLocalBinding::Object(value) => collect_c_value_bitvector_variables(value, variables),
            CLocalBinding::ArrayObject { .. } => {}
        }
    }
    collect_memory_bitvector_variables(&state.memory, variables);
}

fn collect_c_function_bitvector_variables(
    function: &CFunction,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_statement_bitvector_variables(function.body(), variables);
}

fn collect_c_function_specification_bitvector_variables(
    specification: &CFunctionSpecification,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_state_bitvector_variables(specification.state(), variables);
    for argument in specification.arguments() {
        collect_c_expression_bitvector_variables(argument, variables);
    }
    for requirement in specification.requires() {
        collect_proposition_bitvector_variables(requirement, variables);
    }
    collect_c_function_outcome_bitvector_variables(specification.outcome(), variables);
}

fn collect_c_memory_range_bitvector_variables(
    range: &CMemoryRange,
    variables: &mut BTreeSet<Variable>,
) {
    collect_pointer_bitvector_variables(&range.base, variables);
    collect_bitvector_variables(&range.start, variables);
    collect_bitvector_variables(&range.end, variables);
}

fn collect_condition_bitvector_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_bitvector_variables(left, variables);
            collect_pointer_offset_bitvector_variables(right, variables);
        }
    }
}

fn collect_bitvector_variables(term: &Bitvector32Term, variables: &mut BTreeSet<Variable>) {
    match term {
        Bitvector32Term::Constant(_) => {}
        Bitvector32Term::Variable(variable) => {
            variables.insert(*variable);
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right) => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_variables(condition, variables);
            collect_bitvector_variables(then_term, variables);
            collect_bitvector_variables(else_term, variables);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_variables(start, variables);
            collect_bitvector_variables(end, variables);
            collect_bitvector_variables(initial, variables);
            collect_bitvector_variables(body, variables);
            variables.remove(accumulator);
            variables.remove(item);
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
    }
}

fn collect_pointer_offset_bitvector_variables(
    offset: &PointerOffsetTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_bitvector_variables(left, variables);
            collect_pointer_offset_bitvector_variables(right, variables);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => {
            collect_bitvector_variables(value, variables);
        }
    }
}

fn collect_pointer_bitvector_variables(pointer: &Pointer, variables: &mut BTreeSet<Variable>) {
    collect_pointer_offset_bitvector_variables(&pointer.offset, variables);
}

fn collect_memory_bitvector_variables(memory: &CMemory, variables: &mut BTreeSet<Variable>) {
    for (pointer, value) in &memory.cells {
        collect_pointer_bitvector_variables(pointer, variables);
        collect_c_value_bitvector_variables(value, variables);
    }
}

fn collect_c_value_bitvector_variables(value: &CValue, variables: &mut BTreeSet<Variable>) {
    match value {
        CValue::Int32(bits) => collect_bitvector_variables(bits, variables),
        CValue::Pointer(pointer) => collect_pointer_bitvector_variables(pointer, variables),
    }
}

fn substitute_bitvector_variable_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &Bitvector32Term,
) -> Proposition {
    match proposition {
        Proposition::Equal(left, right) => Proposition::Equal(
            substitute_bitvector_variable_in_term(left, from, to),
            substitute_bitvector_variable_in_term(right, from, to),
        ),
        Proposition::ConditionIs(condition, value) => Proposition::ConditionIs(
            substitute_bitvector_variable_in_condition(condition, from, to),
            *value,
        ),
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_term(argument, from, to))
                .collect(),
        },
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => Proposition::CExpressionEvaluates {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            expression: substitute_bitvector_variable_in_c_expression(expression, from, to),
            outcome: substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        },
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        } => Proposition::CStatementExecutes {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            statement: substitute_bitvector_variable_in_c_statement(statement, from, to),
            outcome: substitute_bitvector_variable_in_c_statement_outcome(outcome, from, to),
        },
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => Proposition::CFunctionExecutes {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            function: substitute_bitvector_variable_in_c_function(function, from, to),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            outcome: substitute_bitvector_variable_in_c_function_outcome(outcome, from, to),
        },
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionSatisfiesSpecification {
            function: substitute_bitvector_variable_in_c_function(function, from, to),
            specification: substitute_bitvector_variable_in_c_function_specification(
                specification,
                from,
                to,
            ),
        },
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => Proposition::CMemoryLoads {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_pointer(pointer, from, to),
            outcome: substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        },
        Proposition::CMemoryCanLoad { memory, pointer } => Proposition::CMemoryCanLoad {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_pointer(pointer, from, to),
        },
        Proposition::CMemoryCanStore { memory, pointer } => Proposition::CMemoryCanStore {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_pointer(pointer, from, to),
        },
        Proposition::CMemoryValidRange {
            memory,
            base,
            bytes,
        } => Proposition::CMemoryValidRange {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            base: substitute_bitvector_variable_in_pointer(base, from, to),
            bytes: substitute_bitvector_variable(bytes, from, to),
        },
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => Proposition::CMemoryDisjoint {
            left_base: substitute_bitvector_variable_in_pointer(left_base, from, to),
            left_start: substitute_bitvector_variable(left_start, from, to),
            left_end: substitute_bitvector_variable(left_end, from, to),
            right_base: substitute_bitvector_variable_in_pointer(right_base, from, to),
            right_start: substitute_bitvector_variable(right_start, from, to),
            right_end: substitute_bitvector_variable(right_end, from, to),
        },
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers,
        } => Proposition::CMemoryMutatesOnly {
            before: substitute_bitvector_variable_in_memory(before, from, to),
            after: substitute_bitvector_variable_in_memory(after, from, to),
            pointers: pointers
                .iter()
                .map(|pointer| substitute_bitvector_variable_in_pointer(pointer, from, to))
                .collect(),
        },
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => Proposition::CMemoryEffectSummary {
            before: substitute_bitvector_variable_in_memory(before, from, to),
            after: substitute_bitvector_variable_in_memory(after, from, to),
            mutable_ranges: mutable_ranges
                .iter()
                .map(|range| substitute_bitvector_variable_in_c_memory_range(range, from, to))
                .collect(),
        },
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition,
        } => Proposition::CWhileInvariantRule {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            invariant: invariant
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            body: substitute_bitvector_variable_in_c_statement(body, from, to),
            preserved: preserved
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            postcondition: Box::new(substitute_bitvector_variable_in_proposition(
                postcondition,
                from,
                to,
            )),
        },
        Proposition::And(left, right) => Proposition::And(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::Not(body) => Proposition::Not(Box::new(
            substitute_bitvector_variable_in_proposition(body, from, to),
        )),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::ForAll { var, sort, body } if *var != from => Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: Box::new(substitute_bitvector_variable_in_proposition(body, from, to)),
        },
        proposition => proposition.clone(),
    }
}

fn substitute_bitvector_variable_in_term(
    term: &Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Term {
    match term {
        Term::Condition(condition) => Term::Condition(substitute_bitvector_variable_in_condition(
            condition, from, to,
        )),
        Term::Bitvector32(bits) => Term::Bitvector32(substitute_bitvector_variable(bits, from, to)),
        Term::PointerOffset(offset) => Term::PointerOffset(
            substitute_bitvector_variable_in_pointer_offset(offset, from, to),
        ),
        Term::CValue(value) => {
            Term::CValue(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        Term::CExpressionOutcome(outcome) => Term::CExpressionOutcome(
            substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        ),
        Term::CStatementOutcome(outcome) => Term::CStatementOutcome(
            substitute_bitvector_variable_in_c_statement_outcome(outcome, from, to),
        ),
        Term::CFunctionOutcome(outcome) => Term::CFunctionOutcome(
            substitute_bitvector_variable_in_c_function_outcome(outcome, from, to),
        ),
        Term::CMemory(memory) => {
            Term::CMemory(substitute_bitvector_variable_in_memory(memory, from, to))
        }
        Term::CState(state) => {
            Term::CState(substitute_bitvector_variable_in_c_state(state, from, to))
        }
    }
}

fn substitute_bitvector_variable_in_c_expression(
    expression: &CExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> CExpression {
    match expression {
        CExpression::Value(value) => {
            CExpression::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        CExpression::Variable(name) => CExpression::Variable(name.clone()),
        CExpression::AddressOf(body) => CExpression::AddressOf(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::Not(body) => CExpression::Not(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::Load(body) => CExpression::Load(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::LessThan(left, right) => CExpression::LessThan(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::LessEqual(left, right) => CExpression::LessEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::GreaterThan(left, right) => CExpression::GreaterThan(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::GreaterEqual(left, right) => CExpression::GreaterEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Equal(left, right) => CExpression::Equal(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::NotEqual(left, right) => CExpression::NotEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::And(left, right) => CExpression::And(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Or(left, right) => CExpression::Or(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Add(left, right) => CExpression::Add(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Subtract(left, right) => CExpression::Subtract(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Index(left, right) => CExpression::Index(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
    }
}

fn substitute_bitvector_variable_in_c_statement(
    statement: &CStatement,
    from: Variable,
    to: &Bitvector32Term,
) -> CStatement {
    match statement {
        CStatement::Declare { name, c_type } => CStatement::Declare {
            name: name.clone(),
            c_type: *c_type,
        },
        CStatement::Assign { name, expression } => CStatement::Assign {
            name: name.clone(),
            expression: substitute_bitvector_variable_in_c_expression(expression, from, to),
        },
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => CStatement::CallAssign {
            target: target.clone(),
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
        },
        CStatement::Assert { condition, label } => CStatement::Assert {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            label: label.clone(),
        },
        CStatement::Seq(first, second) => CStatement::Seq(
            Box::new(substitute_bitvector_variable_in_c_statement(
                first, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_statement(
                second, from, to,
            )),
        ),
        CStatement::Return(expression) => CStatement::Return(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        ),
        CStatement::Store { pointer, value } => CStatement::Store {
            pointer: substitute_bitvector_variable_in_c_expression(pointer, from, to),
            value: substitute_bitvector_variable_in_c_expression(value, from, to),
        },
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => CStatement::If {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            then_branch: Box::new(substitute_bitvector_variable_in_c_statement(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_bitvector_variable_in_c_statement(
                else_branch,
                from,
                to,
            )),
        },
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
        } => CStatement::While {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            invariant: invariant
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            invariant_checks: invariant_checks
                .iter()
                .map(|check| CLoopInvariantCheck {
                    proposition: substitute_bitvector_variable_in_c_proposition(
                        check.proposition(),
                        from,
                        to,
                    ),
                    entry_context: check.entry_context.clone(),
                    preservation_context: check.preservation_context.clone(),
                })
                .collect(),
            effect_checks: effect_checks
                .iter()
                .map(|check| CLoopEffectCheck {
                    effect: substitute_bitvector_variable_in_loop_effect(check.effect(), from, to),
                    span: check.span,
                    context: check.context.clone(),
                })
                .collect(),
            body: Box::new(substitute_bitvector_variable_in_c_statement(body, from, to)),
        },
    }
}

fn substitute_bitvector_variable_in_c_proposition(
    proposition: &CProposition,
    from: Variable,
    to: &Bitvector32Term,
) -> CProposition {
    match proposition {
        CProposition::Comparison {
            left,
            operator,
            right,
        } => CProposition::Comparison {
            left: substitute_bitvector_variable_in_c_expression(left, from, to),
            operator: *operator,
            right: substitute_bitvector_variable_in_c_expression(right, from, to),
        },
        CProposition::And(left, right) => CProposition::And(
            Box::new(substitute_bitvector_variable_in_c_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_proposition(
                right, from, to,
            )),
        ),
        CProposition::Or(left, right) => CProposition::Or(
            Box::new(substitute_bitvector_variable_in_c_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_proposition(
                right, from, to,
            )),
        ),
        CProposition::Not(body) => CProposition::Not(Box::new(
            substitute_bitvector_variable_in_c_proposition(body, from, to),
        )),
        CProposition::Implies(left, right) => CProposition::Implies(
            Box::new(substitute_bitvector_variable_in_c_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_proposition(
                right, from, to,
            )),
        ),
        CProposition::ForAllInt32 {
            name,
            variable,
            body,
        } if *variable != from => CProposition::ForAllInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_bitvector_variable_in_c_proposition(
                body, from, to,
            )),
        },
        CProposition::Predicate { name, arguments } => CProposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
        },
        proposition => proposition.clone(),
    }
}

fn substitute_bitvector_variable_in_loop_effect(
    effect: &CLoopEffect,
    from: Variable,
    to: &Bitvector32Term,
) -> CLoopEffect {
    match effect {
        CLoopEffect::Immutable => CLoopEffect::Immutable,
        CLoopEffect::Mutable(segments) => CLoopEffect::Mutable(
            segments
                .iter()
                .map(|segment| CMemorySegment {
                    base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
                    start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
                    end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
                })
                .collect(),
        ),
    }
}

fn substitute_bitvector_variable_in_c_expression_outcome(
    outcome: &CExpressionOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CExpressionOutcome {
    match outcome {
        CExpressionOutcome::Value(value) => {
            CExpressionOutcome::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        CExpressionOutcome::UndefinedBehavior(kind) => {
            CExpressionOutcome::UndefinedBehavior(kind.clone())
        }
        CExpressionOutcome::RuntimeError(kind) => CExpressionOutcome::RuntimeError(kind.clone()),
    }
}

fn substitute_bitvector_variable_in_c_statement_outcome(
    outcome: &CStatementOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CStatementOutcome {
    match outcome {
        CStatementOutcome::Normal(state) => {
            CStatementOutcome::Normal(substitute_bitvector_variable_in_c_state(state, from, to))
        }
        CStatementOutcome::Return { value, state } => CStatementOutcome::Return {
            value: substitute_bitvector_variable_in_c_value(value, from, to),
            state: substitute_bitvector_variable_in_c_state(state, from, to),
        },
        CStatementOutcome::UndefinedBehavior(kind) => {
            CStatementOutcome::UndefinedBehavior(kind.clone())
        }
        CStatementOutcome::RuntimeError(kind) => CStatementOutcome::RuntimeError(kind.clone()),
    }
}

fn substitute_bitvector_variable_in_c_function_outcome(
    outcome: &CFunctionOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunctionOutcome {
    match outcome {
        CFunctionOutcome::Return { value, state } => CFunctionOutcome::Return {
            value: substitute_bitvector_variable_in_c_value(value, from, to),
            state: substitute_bitvector_variable_in_c_state(state, from, to),
        },
        CFunctionOutcome::UndefinedBehavior(kind) => {
            CFunctionOutcome::UndefinedBehavior(kind.clone())
        }
        CFunctionOutcome::RuntimeError(kind) => CFunctionOutcome::RuntimeError(kind.clone()),
    }
}

fn substitute_bitvector_variable_in_c_state(
    state: &CState,
    from: Variable,
    to: &Bitvector32Term,
) -> CState {
    let bindings = state
        .locals
        .bindings
        .iter()
        .map(|(name, binding)| {
            let binding = match binding {
                CLocalBinding::Object(value) => {
                    CLocalBinding::Object(substitute_bitvector_variable_in_c_value(value, from, to))
                }
                CLocalBinding::ArrayObject {
                    element_type,
                    length,
                } => CLocalBinding::ArrayObject {
                    element_type: *element_type,
                    length: *length,
                },
            };
            (name.clone(), binding)
        })
        .collect();
    CState {
        locals: CLocalEnvironment { bindings },
        memory: substitute_bitvector_variable_in_memory(&state.memory, from, to),
    }
}

fn substitute_bitvector_variable_in_c_function(
    function: &CFunction,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunction {
    CFunction {
        return_type: function.return_type,
        name: function.name.clone(),
        parameters: function.parameters.clone(),
        body: substitute_bitvector_variable_in_c_statement(function.body(), from, to),
    }
}

fn substitute_bitvector_variable_in_c_function_specification(
    specification: &CFunctionSpecification,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunctionSpecification {
    CFunctionSpecification {
        state: substitute_bitvector_variable_in_c_state(specification.state(), from, to),
        arguments: specification
            .arguments()
            .iter()
            .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
            .collect(),
        requires: specification
            .requires()
            .iter()
            .map(|requirement| substitute_bitvector_variable_in_proposition(requirement, from, to))
            .collect(),
        outcome: substitute_bitvector_variable_in_c_function_outcome(
            specification.outcome(),
            from,
            to,
        ),
    }
}

fn substitute_bitvector_variable_in_c_memory_range(
    range: &CMemoryRange,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemoryRange {
    CMemoryRange {
        base: substitute_bitvector_variable_in_pointer(&range.base, from, to),
        start: substitute_bitvector_variable(&range.start, from, to),
        end: substitute_bitvector_variable(&range.end, from, to),
    }
}

fn substitute_bitvector_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> ConditionTerm {
    match condition {
        ConditionTerm::Constant(value) => ConditionTerm::Constant(*value),
        ConditionTerm::Variable(variable) => ConditionTerm::Variable(*variable),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => ConditionTerm::signed_less_than(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => ConditionTerm::signed_less_equal(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            ConditionTerm::signed_greater_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            ConditionTerm::signed_greater_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32Equal(left, right) => ConditionTerm::equal(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            ConditionTerm::signed_add_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            ConditionTerm::signed_subtract_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::pointer_offset_equal(
            substitute_bitvector_variable_in_pointer_offset(left, from, to),
            substitute_bitvector_variable_in_pointer_offset(right, from, to),
        ),
    }
}

fn substitute_bitvector_variable(
    term: &Bitvector32Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(*value),
        Bitvector32Term::Variable(variable) if *variable == from => to.clone(),
        Bitvector32Term::Variable(variable) => Bitvector32Term::Variable(*variable),
        Bitvector32Term::Add(left, right) => Bitvector32Term::add(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Subtract(left, right) => Bitvector32Term::subtract(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Multiply(left, right) => Bitvector32Term::Multiply(
            Box::new(substitute_bitvector_variable(left, from, to)),
            Box::new(substitute_bitvector_variable(right, from, to)),
        ),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::if_then_else(
            substitute_bitvector_variable_in_condition(condition, from, to),
            substitute_bitvector_variable(then_term, from, to),
            substitute_bitvector_variable(else_term, from, to),
        ),
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let body = if *accumulator == from || *item == from {
                body.as_ref().clone()
            } else {
                substitute_bitvector_variable(body, from, to)
            };
            Bitvector32Term::range_fold(
                substitute_bitvector_variable(start, from, to),
                substitute_bitvector_variable(end, from, to),
                substitute_bitvector_variable(initial, from, to),
                *accumulator,
                *item,
                body,
            )
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => Bitvector32Term::MemoryLoad(
            Box::new(substitute_bitvector_variable_in_memory(memory, from, to)),
            Box::new(substitute_bitvector_variable_in_pointer(pointer, from, to)),
        ),
    }
}

fn substitute_bitvector_variable_in_pointer_offset(
    offset: &PointerOffsetTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> PointerOffsetTerm {
    match offset {
        PointerOffsetTerm::Constant(value) => PointerOffsetTerm::Constant(*value),
        PointerOffsetTerm::Variable(variable) => PointerOffsetTerm::Variable(*variable),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            substitute_bitvector_variable_in_pointer_offset(left, from, to),
            substitute_bitvector_variable_in_pointer_offset(right, from, to),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
            substitute_bitvector_variable(value, from, to),
            *byte_width,
        ),
    }
}

fn substitute_bitvector_variable_in_pointer(
    pointer: &Pointer,
    from: Variable,
    to: &Bitvector32Term,
) -> Pointer {
    Pointer {
        block: pointer.block.clone(),
        offset: substitute_bitvector_variable_in_pointer_offset(&pointer.offset, from, to),
    }
}

fn substitute_bitvector_variable_in_memory(
    memory: &CMemory,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemory {
    let cells = memory
        .cells
        .iter()
        .map(|(pointer, value)| {
            (
                substitute_bitvector_variable_in_pointer(pointer, from, to),
                substitute_bitvector_variable_in_c_value(value, from, to),
            )
        })
        .collect();
    CMemory {
        blocks: memory.blocks.clone(),
        cells,
    }
}

fn substitute_bitvector_variable_in_c_value(
    value: &CValue,
    from: Variable,
    to: &Bitvector32Term,
) -> CValue {
    match value {
        CValue::Int32(bits) => int32(substitute_bitvector_variable(bits, from, to)),
        CValue::Pointer(pointer) => {
            CValue::Pointer(substitute_bitvector_variable_in_pointer(pointer, from, to))
        }
    }
}

fn memory_range_still_available(
    range_memory: &CMemory,
    current_memory: &CMemory,
    base: &Pointer,
) -> bool {
    range_memory == current_memory
        || range_memory.has_block(&base.block) == current_memory.has_block(&base.block)
}

fn forall_int32(var: Variable, body: Proposition) -> Proposition {
    Proposition::ForAll {
        var,
        sort: Sort::CInt32,
        body: Box::new(body),
    }
}

fn wrap_proof_facts(
    proposition: Proposition,
    assumptions: &Assumptions,
    facts: &[PathFact],
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .filter(|obligation| obligation.is_assumable())
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    let proposition = facts
        .iter()
        .filter(|fact| fact.is_public())
        .rev()
        .fold(proposition, |body, fact| {
            Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
        });

    let proposition = assumptions
        .prop_facts
        .iter()
        .rev()
        .fold(proposition, |body, proposition| {
            Proposition::Implies(Box::new(proposition.clone()), Box::new(body))
        });

    assumptions
        .condition_facts
        .iter()
        .rev()
        .fold(proposition, |body, (condition, value)| {
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition.clone(), *value)),
                Box::new(body),
            )
        })
}

fn wrap_path_context(
    proposition: Proposition,
    facts: &[PathFact],
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .filter(|obligation| obligation.is_assumable())
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    facts.iter().rev().fold(proposition, |body, fact| {
        Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
    })
}

fn public_path_facts(facts: &[PathFact]) -> Vec<PathFact> {
    facts
        .iter()
        .filter(|fact| fact.is_public())
        .cloned()
        .collect()
}

fn solve_builtin_prop(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::Equal(left, right) => left == right,
        Proposition::ConditionIs(ConditionTerm::Constant(actual), expected) => actual == expected,
        Proposition::And(left, right) => solve_builtin_prop(left) && solve_builtin_prop(right),
        Proposition::Or(left, right) => solve_builtin_prop(left) || solve_builtin_prop(right),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(ConditionTerm::Constant(actual), expected) => {
                actual != expected
            }
            _ => false,
        },
        Proposition::CMemoryValidRange {
            memory,
            base,
            bytes,
        } => bytes
            .as_const()
            .is_some_and(|bytes| memory.access_in_bounds(base, bytes)),
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => memory_ranges_disjoint_builtin(
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        ),
        Proposition::CMemoryCanLoad { memory, pointer } => memory.can_load_concretely(pointer, 4),
        Proposition::CMemoryCanStore { memory, pointer } => memory.access_in_bounds(pointer, 4),
        _ => false,
    }
}

fn memory_ranges_disjoint_builtin(
    left_base: &Pointer,
    left_start: &Bitvector32Term,
    left_end: &Bitvector32Term,
    right_base: &Pointer,
    right_start: &Bitvector32Term,
    right_end: &Bitvector32Term,
) -> bool {
    if left_base.block != right_base.block {
        return true;
    }

    let Some(left_base_index) = left_base.element_index_from_base(&Pointer {
        block: left_base.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    }) else {
        return false;
    };
    let Some(right_base_index) = right_base.element_index_from_base(&Pointer {
        block: right_base.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    }) else {
        return false;
    };
    let (Some(left_base_index), Some(left_start), Some(left_end)) = (
        signed_bitvector_constant(&left_base_index),
        signed_bitvector_constant(left_start),
        signed_bitvector_constant(left_end),
    ) else {
        return false;
    };
    let (Some(right_base_index), Some(right_start), Some(right_end)) = (
        signed_bitvector_constant(&right_base_index),
        signed_bitvector_constant(right_start),
        signed_bitvector_constant(right_end),
    ) else {
        return false;
    };

    let left_start = left_base_index + left_start;
    let left_end = left_base_index + left_end;
    let right_start = right_base_index + right_start;
    let right_end = right_base_index + right_end;
    left_end <= right_start || right_end <= left_start
}

fn int32_element_index_from_offset(offset: &PointerOffsetTerm) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            int32_element_index_from_offset(right)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            int32_element_index_from_offset(left)
        }
        PointerOffsetTerm::Add(left, right) => Some(Bitvector32Term::add(
            int32_element_index_from_offset(left)?,
            int32_element_index_from_offset(right)?,
        )),
        PointerOffsetTerm::Int32Scaled { value, byte_width } if *byte_width == 4 => {
            Some(value.as_ref().clone())
        }
        PointerOffsetTerm::Constant(offset) if offset % 4 == 0 => {
            let index = offset / 4;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        _ => None,
    }
}

fn int32_element_count_from_bytes(bytes: &Bitvector32Term) -> Option<Bitvector32Term> {
    match bytes {
        Bitvector32Term::Multiply(left, right)
            if right.as_ref() == &Bitvector32Term::Constant(4) =>
        {
            Some(left.as_ref().clone())
        }
        Bitvector32Term::Multiply(left, right)
            if left.as_ref() == &Bitvector32Term::Constant(4) =>
        {
            Some(right.as_ref().clone())
        }
        Bitvector32Term::Constant(bytes) if bytes % 4 == 0 => {
            Some(Bitvector32Term::Constant(bytes / 4))
        }
        _ => None,
    }
}

fn signed_const_add(term: &Bitvector32Term, addend: u32) -> Option<Bitvector32Term> {
    let addend = i32::try_from(addend).ok()?;
    let sum = (term.as_const()? as i32).checked_add(addend)?;
    Some(Bitvector32Term::Constant(sum as u32))
}

fn add_path_fact(
    facts: &mut Vec<PathFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
) -> Option<()> {
    add_path_fact_with_visibility(facts, assumptions, proposition, true)
}

fn add_internal_path_fact(
    facts: &mut Vec<PathFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
) -> Option<()> {
    add_path_fact_with_visibility(facts, assumptions, proposition, false)
}

fn add_path_fact_with_visibility(
    facts: &mut Vec<PathFact>,
    assumptions: &Assumptions,
    proposition: Proposition,
    public: bool,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_path_fact(facts, assumptions, condition, value);
    }

    if assumptions.proves(&proposition) || facts.iter().any(|fact| fact.proposition == proposition)
    {
        return Some(());
    }

    facts.push(if public {
        PathFact::new(proposition)
    } else {
        PathFact::internal(proposition)
    });
    Some(())
}

fn add_condition_path_fact(
    facts: &mut Vec<PathFact>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    if let Some(known) = assumptions.decide(&condition) {
        return (known == value).then_some(());
    }

    if let Some(existing) = facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::ConditionIs(existing_condition, existing_value)
                if existing_condition == &condition =>
            {
                Some(*existing_value)
            }
            _ => None,
        })
        .next()
    {
        return (existing == value).then_some(());
    }

    facts.push(PathFact::condition(condition, value));
    Some(())
}

fn add_pointer_offset_equality_path_facts(
    facts: &mut Vec<PathFact>,
    assumptions: &Assumptions,
    left: PointerOffsetTerm,
    right: PointerOffsetTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact(
        facts,
        assumptions,
        ConditionTerm::pointer_offset_equal(left.clone(), right.clone()),
        value,
    )?;

    if let (Some(left_index), Some(right_index)) = (
        int32_element_index_from_offset(&left),
        int32_element_index_from_offset(&right),
    ) {
        add_condition_path_fact(
            facts,
            assumptions,
            ConditionTerm::equal(left_index, right_index),
            value,
        )?;
    }

    Some(())
}

fn add_proof_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
) -> Option<()> {
    add_proof_obligation_with_context(obligations, assumptions, proposition, None)
}

fn add_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
    context: Option<&str>,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_obligation(obligations, assumptions, condition, value, context);
    }

    if assumptions.proves(&proposition)
        || obligations
            .iter()
            .any(|obligation| obligation.proposition == proposition)
    {
        return Some(());
    }

    let obligation = ProofObligation::new(proposition);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
    Some(())
}

fn add_required_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    proposition: Proposition,
    context: Option<&str>,
) {
    if assumptions.proves(&proposition)
        || obligations
            .iter()
            .any(|obligation| obligation.proposition == proposition)
    {
        return;
    }

    let obligation = ProofObligation::verification_condition(proposition);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
}

fn append_required_proof_obligations(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_with_context(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
        );
    }
}

fn append_required_proof_obligations_under_path_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    new_obligations: &[ProofObligation],
    facts: &[PathFact],
    context_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_with_context(
            obligations,
            assumptions,
            wrap_path_context(obligation.proposition().clone(), facts, context_obligations),
            obligation.context(),
        );
    }
}

fn add_condition_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
    condition: ConditionTerm,
    value: bool,
    context: Option<&str>,
) -> Option<()> {
    if let Some(known) = assumptions.decide(&condition) {
        return (known == value).then_some(());
    }

    if let Some(existing) = obligations
        .iter()
        .filter_map(|obligation| match obligation.proposition() {
            Proposition::ConditionIs(existing_condition, existing_value)
                if existing_condition == &condition =>
            {
                Some(*existing_value)
            }
            _ => None,
        })
        .next()
    {
        return (existing == value).then_some(());
    }

    let obligation = ProofObligation::condition(condition, value);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
    Some(())
}

fn merge_obligations(
    left: &[ProofObligation],
    right: &[ProofObligation],
    assumptions: &Assumptions,
) -> Option<Vec<ProofObligation>> {
    let mut obligations = left.to_vec();
    for obligation in right {
        if obligation.is_assumable() {
            add_proof_obligation_with_context(
                &mut obligations,
                assumptions,
                obligation.proposition().clone(),
                obligation.context(),
            )?;
        } else {
            add_required_proof_obligation_with_context(
                &mut obligations,
                assumptions,
                obligation.proposition().clone(),
                obligation.context(),
            );
        }
    }
    Some(obligations)
}

fn merge_facts(
    left: &[PathFact],
    right: &[PathFact],
    assumptions: &Assumptions,
) -> Option<Vec<PathFact>> {
    let mut facts = left.to_vec();
    for fact in right {
        add_path_fact_with_visibility(
            &mut facts,
            assumptions,
            fact.proposition().clone(),
            fact.is_public(),
        )?;
    }
    Some(facts)
}

fn merge_path_facts_and_obligations(
    left_facts: &[PathFact],
    left_obligations: &[ProofObligation],
    right_facts: &[PathFact],
    right_obligations: &[ProofObligation],
    assumptions: &Assumptions,
) -> Option<(Vec<PathFact>, Vec<ProofObligation>)> {
    let facts = merge_facts(left_facts, right_facts, assumptions)?;
    let obligations = merge_obligations(left_obligations, right_obligations, assumptions)?;
    Some((facts, obligations))
}

fn decide_with_facts(
    assumptions: &Assumptions,
    facts: &[PathFact],
    condition: &ConditionTerm,
) -> Option<bool> {
    assumptions.decide(condition).or_else(|| {
        facts.iter().find_map(|fact| match fact.proposition() {
            Proposition::ConditionIs(existing_condition, value)
                if existing_condition == condition =>
            {
                Some(*value)
            }
            _ => None,
        })
    })
}

fn assumptions_with_path_context(
    assumptions: &Assumptions,
    facts: &[PathFact],
    obligations: &[ProofObligation],
) -> Assumptions {
    let mut assumptions = assumptions.clone();
    for fact in facts {
        assumptions = assumptions.assume_proposition(fact.proposition().clone());
    }
    for obligation in obligations {
        if obligation.is_assumable() {
            assumptions = assumptions.assume_proposition(obligation.proposition().clone());
        }
    }
    assumptions
}

fn assumptions_with_propositions(
    assumptions: &Assumptions,
    propositions: &[Proposition],
) -> Assumptions {
    let mut assumptions = assumptions.clone();
    for proposition in propositions {
        assumptions = assumptions.assume_proposition(proposition.clone());
    }
    assumptions
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CPropositionPath {
    proposition: Proposition,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

fn lower_c_proposition_at_state(
    state: &CState,
    proposition: &CProposition,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CPropositionPath>> {
    match proposition {
        CProposition::Comparison {
            left,
            operator,
            right,
        } => lower_c_comparison_proposition_at_state(
            state,
            left,
            *operator,
            right,
            assumptions,
            budget,
        ),
        CProposition::And(left, right) => {
            let mut paths = Vec::new();
            for left_path in lower_c_proposition_at_state(state, left, assumptions, budget)? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                );
                for right_path in
                    lower_c_proposition_at_state(state, right, &right_assumptions, budget)?
                {
                    if let Some((facts, obligations)) = merge_path_facts_and_obligations(
                        &left_path.facts,
                        &left_path.obligations,
                        &right_path.facts,
                        &right_path.obligations,
                        assumptions,
                    ) {
                        paths.push(CPropositionPath {
                            proposition: Proposition::And(
                                Box::new(left_path.proposition.clone()),
                                Box::new(right_path.proposition),
                            ),
                            facts,
                            obligations,
                        });
                    }
                }
            }
            Ok(paths)
        }
        CProposition::Or(left, right) => lower_c_binary_proposition_at_state(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right| Proposition::Or(Box::new(left), Box::new(right)),
        ),
        CProposition::Not(body) => {
            Ok(
                lower_c_proposition_at_state(state, body, assumptions, budget)?
                    .into_iter()
                    .map(|path| CPropositionPath {
                        proposition: Proposition::Not(Box::new(path.proposition)),
                        facts: path.facts,
                        obligations: path.obligations,
                    })
                    .collect(),
            )
        }
        CProposition::Implies(left, right) => {
            let mut paths = Vec::new();
            for left_path in lower_c_proposition_at_state(state, left, assumptions, budget)? {
                let right_assumptions = assumptions_with_path_context(
                    assumptions,
                    &left_path.facts,
                    &left_path.obligations,
                )
                .assume_proposition(left_path.proposition.clone());
                for right_path in
                    lower_c_proposition_at_state(state, right, &right_assumptions, budget)?
                {
                    let guarded_right_obligations = right_path
                        .obligations
                        .iter()
                        .cloned()
                        .map(|obligation| {
                            let antecedent = left_path.proposition.clone();
                            obligation.map_proposition(|proposition| {
                                Proposition::Implies(Box::new(antecedent), Box::new(proposition))
                            })
                        })
                        .collect::<Vec<_>>();
                    if let Some((facts, obligations)) = merge_path_facts_and_obligations(
                        &left_path.facts,
                        &left_path.obligations,
                        &right_path.facts,
                        &guarded_right_obligations,
                        assumptions,
                    ) {
                        paths.push(CPropositionPath {
                            proposition: Proposition::Implies(
                                Box::new(left_path.proposition.clone()),
                                Box::new(right_path.proposition),
                            ),
                            facts,
                            obligations,
                        });
                    }
                }
            }
            Ok(paths)
        }
        CProposition::ForAllInt32 {
            name,
            variable,
            body,
        } => {
            let mut state = state.clone();
            state
                .locals
                .set(name.clone(), int32(Bitvector32Term::Variable(*variable)));
            Ok(
                lower_c_proposition_at_state(&state, body, assumptions, budget)?
                    .into_iter()
                    .map(|path| CPropositionPath {
                        proposition: Proposition::ForAll {
                            var: *variable,
                            sort: Sort::CInt32,
                            body: Box::new(path.proposition),
                        },
                        facts: path.facts,
                        obligations: path
                            .obligations
                            .into_iter()
                            .map(|obligation| {
                                obligation.map_proposition(|proposition| Proposition::ForAll {
                                    var: *variable,
                                    sort: Sort::CInt32,
                                    body: Box::new(proposition),
                                })
                            })
                            .collect(),
                    })
                    .collect(),
            )
        }
        CProposition::Predicate { name, arguments } => {
            lower_c_predicate_proposition_at_state(state, name, arguments, assumptions, budget)
        }
    }
}

fn lower_c_predicate_proposition_at_state(
    state: &CState,
    name: &str,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CPropositionPath>> {
    let mut paths = vec![CPropositionPath {
        proposition: Proposition::Predicate {
            name: name.to_string(),
            arguments: vec![Term::CMemory(state.memory().clone())],
        },
        facts: Vec::new(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let argument_paths = evaluate_c_expression_paths(state, argument, assumptions, budget)?;
        let mut next_paths = Vec::new();
        for prefix_path in paths {
            let path_assumptions = assumptions_with_path_context(
                assumptions,
                &prefix_path.facts,
                &prefix_path.obligations,
            );
            for argument_path in &argument_paths {
                let CExpressionOutcome::Value(value) = &argument_path.outcome else {
                    continue;
                };
                let Some((facts, obligations)) = merge_path_facts_and_obligations(
                    &prefix_path.facts,
                    &prefix_path.obligations,
                    &argument_path.facts,
                    &argument_path.obligations,
                    &path_assumptions,
                ) else {
                    continue;
                };
                let Proposition::Predicate {
                    name,
                    mut arguments,
                } = prefix_path.proposition.clone()
                else {
                    unreachable!("predicate lowering should carry predicate propositions")
                };
                arguments.push(Term::CValue(value.clone()));
                next_paths.push(CPropositionPath {
                    proposition: Proposition::Predicate { name, arguments },
                    facts,
                    obligations,
                });
            }
        }
        paths = next_paths;
    }

    Ok(paths)
}

fn lower_c_binary_proposition_at_state(
    state: &CState,
    left: &CProposition,
    right: &CProposition,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
    combine: impl Fn(Proposition, Proposition) -> Proposition,
) -> ExecutionResult<Vec<CPropositionPath>> {
    let mut paths = Vec::new();
    for left_path in lower_c_proposition_at_state(state, left, assumptions, budget)? {
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in lower_c_proposition_at_state(state, right, &right_assumptions, budget)? {
            if let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) {
                paths.push(CPropositionPath {
                    proposition: combine(left_path.proposition.clone(), right_path.proposition),
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

fn lower_c_comparison_proposition_at_state(
    state: &CState,
    left: &CExpression,
    operator: CComparisonOperator,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CPropositionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionOutcome::Value(left) = left_path.outcome else {
            continue;
        };
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let CExpressionOutcome::Value(right) = right_path.outcome else {
                continue;
            };
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            if let Some(proposition) = c_value_comparison_proposition(&left, operator, &right) {
                paths.push(CPropositionPath {
                    proposition,
                    facts,
                    obligations,
                });
            }
        }
    }
    Ok(paths)
}

fn c_value_comparison_proposition(
    left: &CValue,
    operator: CComparisonOperator,
    right: &CValue,
) -> Option<Proposition> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => {
            let (condition, value) = match operator {
                CComparisonOperator::Equal => {
                    (ConditionTerm::equal(left.clone(), right.clone()), true)
                }
                CComparisonOperator::NotEqual => {
                    (ConditionTerm::equal(left.clone(), right.clone()), false)
                }
                CComparisonOperator::LessThan => (
                    ConditionTerm::signed_less_than(left.clone(), right.clone()),
                    true,
                ),
                CComparisonOperator::LessEqual => (
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                ),
                CComparisonOperator::GreaterThan => (
                    ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                    true,
                ),
                CComparisonOperator::GreaterEqual => (
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                ),
            };
            Some(Proposition::ConditionIs(condition, value))
        }
        _ => None,
    }
}

fn evaluate_c_expression(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> Option<CExpressionOutcome> {
    let paths = evaluate_c_expression_paths(state, expression, assumptions, budget).ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.obligations.is_empty() {
        return None;
    }
    Some(path.outcome)
}

fn evaluate_c_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        CExpression::Value(value) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpression::Variable(name) if state.locals.is_array_object(name) => {
            let pointer = CMemory::local_pointer(name);
            vec![CExpressionPath {
                outcome: if state.memory.has_block(&pointer.block) {
                    CExpressionOutcome::Value(CValue::Pointer(pointer))
                } else {
                    CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone()))
                },
                facts: Vec::new(),
                obligations: Vec::new(),
            }]
        }
        CExpression::Variable(_) => {
            read_c_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
        CExpression::AddressOf(target) => {
            address_of_lvalue_paths(state, target, assumptions, budget)?
        }
        CExpression::LessThan(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                condition_as_c_int32_paths(
                    ConditionTerm::signed_less_than(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        )?,
        CExpression::LessEqual(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                condition_as_c_int32_paths(
                    ConditionTerm::signed_less_equal(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        )?,
        CExpression::GreaterThan(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                condition_as_c_int32_paths(
                    ConditionTerm::signed_greater_than(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        )?,
        CExpression::GreaterEqual(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                condition_as_c_int32_paths(
                    ConditionTerm::signed_greater_equal(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        )?,
        CExpression::Equal(left, right) => {
            evaluate_c_equal_paths(state, left, right, assumptions, budget)?
        }
        CExpression::NotEqual(left, right) => {
            evaluate_c_not_equal_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Not(expression) => {
            evaluate_c_not_paths(state, expression, assumptions, budget)?
        }
        CExpression::And(left, right) => {
            evaluate_c_logical_and_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Or(left, right) => {
            evaluate_c_logical_or_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Add(left, right) => {
            evaluate_c_add_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Subtract(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_subtract(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::Load(_) | CExpression::Index(_, _) => {
            read_c_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
    };
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn evaluate_c_lvalue_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CLValuePath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        CExpression::Variable(name) => vec![CLValuePath {
            outcome: match state.locals.binding(name) {
                Some(CLocalBinding::Object(value)) => {
                    CLValueOutcome::LValue(CLValue::local(name.clone(), value.c_type()))
                }
                Some(CLocalBinding::ArrayObject { .. }) => {
                    CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                }
                None => CLValueOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone())),
            },
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpression::Load(pointer_expression) => {
            let mut paths = Vec::new();
            for pointer_path in
                evaluate_c_expression_paths(state, pointer_expression, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(CLValue::memory(pointer, CType::Int32)),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::Value(_) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => CLValuePath {
                        outcome: CLValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::RuntimeError(error) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        CExpression::Index(base, index) => {
            let mut paths = Vec::new();
            for pointer_path in evaluate_c_add_paths(state, base, index, assumptions, budget)? {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(CLValue::memory(pointer, CType::Int32)),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::Value(_) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => CLValuePath {
                        outcome: CLValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::RuntimeError(error) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        _ => vec![CLValuePath {
            outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
    };
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn read_c_lvalue_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for lvalue_path in evaluate_c_lvalue_paths(state, expression, assumptions, budget)? {
        paths.extend(read_c_lvalue_paths(
            state,
            lvalue_path.outcome,
            lvalue_path.facts,
            lvalue_path.obligations,
            assumptions,
        ));
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn read_c_lvalue_paths(
    state: &CState,
    outcome: CLValueOutcome,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match outcome {
        CLValueOutcome::LValue(lvalue) => match &lvalue.storage {
            CLValueStorage::Local { name } => vec![CExpressionPath {
                outcome: match state.locals.get(name) {
                    Some(value) if lvalue.value_type.accepts(value) => {
                        CExpressionOutcome::Value(value.clone())
                    }
                    Some(_) => CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    None => CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(
                        name.clone(),
                    )),
                },
                facts,
                obligations,
            }],
            CLValueStorage::Memory { pointer } => evaluate_c_memory_load_paths(
                &state.memory,
                pointer.clone(),
                lvalue.value_type,
                facts,
                obligations,
                assumptions,
            ),
        },
        CLValueOutcome::UndefinedBehavior(undefined_behavior) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
            facts,
            obligations,
        }],
        CLValueOutcome::RuntimeError(error) => vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(error),
            facts,
            obligations,
        }],
    }
}

fn address_of_lvalue_paths(
    state: &CState,
    target: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for lvalue_path in evaluate_c_lvalue_paths(state, target, assumptions, budget)? {
        paths.push(match lvalue_path.outcome {
            CLValueOutcome::LValue(lvalue) => match lvalue.pointer(state) {
                Some(pointer) => CExpressionPath {
                    outcome: CExpressionOutcome::Value(CValue::Pointer(pointer)),
                    facts: lvalue_path.facts,
                    obligations: lvalue_path.obligations,
                },
                None => CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(
                        format!("{target:?}"),
                    )),
                    facts: lvalue_path.facts,
                    obligations: lvalue_path.obligations,
                },
            },
            CLValueOutcome::UndefinedBehavior(undefined_behavior) => CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                facts: lvalue_path.facts,
                obligations: lvalue_path.obligations,
            },
            CLValueOutcome::RuntimeError(error) => CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: lvalue_path.facts,
                obligations: lvalue_path.obligations,
            },
        });
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn condition_as_c_int32_paths(
    condition: ConditionTerm,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match decide_with_facts(assumptions, &facts, &condition) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(1)),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(0)),
            facts,
            obligations,
        }],
        None => {
            let mut true_facts = facts.clone();
            add_condition_path_fact(&mut true_facts, assumptions, condition.clone(), true)
                .expect("unknown comparison fact should be consistent");

            let mut false_facts = facts;
            add_condition_path_fact(&mut false_facts, assumptions, condition, false)
                .expect("unknown comparison fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(1)),
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(0)),
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

fn condition_as_c_int32_not_paths(
    condition: ConditionTerm,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match decide_with_facts(assumptions, &facts, &condition) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(0)),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(1)),
            facts,
            obligations,
        }],
        None => {
            let mut true_facts = facts.clone();
            add_condition_path_fact(&mut true_facts, assumptions, condition.clone(), true)
                .expect("unknown comparison fact should be consistent");

            let mut false_facts = facts;
            add_condition_path_fact(&mut false_facts, assumptions, condition, false)
                .expect("unknown comparison fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(0)),
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(1)),
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CTruthinessPath {
    is_true: bool,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
}

fn c_truthiness_paths(
    value: CValue,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CTruthinessPath> {
    match value {
        CValue::Int32(bits) => {
            let is_zero = ConditionTerm::equal(bits, Bitvector32Term::Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(true) => vec![CTruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![CTruthinessPath {
                    is_true: true,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");

                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");

                    vec![
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::Pointer(pointer) => match (&pointer.block[..], &pointer.offset) {
            ("null", PointerOffsetTerm::Constant(0)) => vec![CTruthinessPath {
                is_true: false,
                facts,
                obligations,
            }],
            _ => vec![CTruthinessPath {
                is_true: true,
                facts,
                obligations,
            }],
        },
    }
}

fn c_truthiness_as_c_int32_paths(
    value: CValue,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    c_truthiness_paths(value, facts, obligations, assumptions)
        .into_iter()
        .map(|path| CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(if path.is_true { 1 } else { 0 })),
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect()
}

fn evaluate_c_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: Vec<PathFact>,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    let memory = memory.without_proven_distinct_cells(&pointer, assumptions);

    if let Some(value) = memory.known_value(&pointer) {
        if !value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        }
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if let Some((stored_pointer, stored_value)) =
        memory.first_unresolved_same_block_cell(&pointer, assumptions)
    {
        let mut paths = Vec::new();

        let mut equal_facts = facts.clone();
        if add_pointer_offset_equality_path_facts(
            &mut equal_facts,
            assumptions,
            pointer.offset.clone(),
            stored_pointer.offset.clone(),
            true,
        )
        .is_some()
        {
            paths.push(CExpressionPath {
                outcome: if value_type.accepts(&stored_value) {
                    CExpressionOutcome::Value(stored_value)
                } else {
                    CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                },
                facts: equal_facts,
                obligations: obligations.clone(),
            });
        }

        let mut distinct_facts = facts;
        if add_pointer_offset_equality_path_facts(
            &mut distinct_facts,
            assumptions,
            pointer.offset.clone(),
            stored_pointer.offset.clone(),
            false,
        )
        .is_some()
        {
            paths.extend(evaluate_c_memory_load_paths(
                &memory.without_cell(&stored_pointer),
                pointer,
                value_type,
                distinct_facts,
                obligations,
                assumptions,
            ));
        }

        return paths;
    }

    if memory.can_load_concretely(&pointer, value_type.byte_width()) {
        if value_type != CType::Int32 {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        }
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(memory.symbolic_int32_load(&pointer)),
            facts,
            obligations,
        }];
    }

    let proposition = Proposition::CMemoryCanLoad {
        memory: memory.clone(),
        pointer: pointer.clone(),
    };
    if add_proof_obligation(&mut obligations, assumptions, proposition).is_none() {
        return Vec::new();
    }

    if value_type != CType::Int32 {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }];
    }

    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(memory.symbolic_int32_load(&pointer)),
        facts,
        obligations,
    }]
}

fn evaluate_c_add_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(value) => value,
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            let right = match right_path.outcome {
                CExpressionOutcome::Value(value) => value,
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    });
                    continue;
                }
                CExpressionOutcome::RuntimeError(error) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    });
                    continue;
                }
            };

            paths.extend(apply_c_add(
                left.clone(),
                right,
                facts,
                obligations,
                assumptions,
            ));
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn apply_c_add(
    left: CValue,
    right: CValue,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => {
            apply_c_int32_add(left, right, facts, obligations, assumptions)
        }
        (CValue::Pointer(pointer), CValue::Int32(offset))
        | (CValue::Int32(offset), CValue::Pointer(pointer)) => {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Pointer(
                    pointer.offset_by_int32_elements(offset),
                )),
                facts,
                obligations,
            }]
        }
        _ => vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }],
    }
}

fn apply_c_int32_add(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_add_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::add(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::add(left, right))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

fn apply_c_int32_subtract(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_subtract_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::subtract(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::subtract(
                        left, right,
                    ))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

fn evaluate_c_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(left) => left,
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExpressionOutcome::Value(right) => {
                    paths.extend(apply_c_equal(
                        left.clone(),
                        right,
                        facts,
                        obligations,
                        assumptions,
                    ));
                }
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn apply_c_equal(
    left: CValue,
    right: CValue,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => condition_as_c_int32_paths(
            ConditionTerm::equal(left, right),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Pointer(left), CValue::Pointer(right)) => condition_as_c_int32_paths(
            pointer_equality_condition(left, right),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_paths(
                pointer_is_null_condition(pointer),
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }],
    }
}

fn evaluate_c_not_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(left) => left,
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExpressionOutcome::Value(right) => {
                    paths.extend(apply_c_not_equal(
                        left.clone(),
                        right,
                        facts,
                        obligations,
                        assumptions,
                    ));
                }
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn apply_c_not_equal(
    left: CValue,
    right: CValue,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (CValue::Int32(left), CValue::Int32(right)) => condition_as_c_int32_not_paths(
            ConditionTerm::equal(left, right),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Pointer(left), CValue::Pointer(right)) => condition_as_c_int32_not_paths(
            pointer_equality_condition(left, right),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_not_paths(
                pointer_is_null_condition(pointer),
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }],
    }
}

fn evaluate_c_not_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                paths.extend(
                    c_truthiness_paths(value, path.facts, path.obligations, assumptions)
                        .into_iter()
                        .map(|truthiness| CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(if truthiness.is_true {
                                0
                            } else {
                                1
                            })),
                            facts: truthiness.facts,
                            obligations: truthiness.obligations,
                        }),
                );
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: path.facts,
                    obligations: path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn evaluate_c_logical_and_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        match left_path.outcome {
            CExpressionOutcome::Value(left_value) => {
                for left_truthiness in c_truthiness_paths(
                    left_value,
                    left_path.facts,
                    left_path.obligations,
                    assumptions,
                ) {
                    if !left_truthiness.is_true {
                        paths.push(CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(0)),
                            facts: left_truthiness.facts,
                            obligations: left_truthiness.obligations,
                        });
                        continue;
                    }

                    let right_assumptions = assumptions_with_path_context(
                        assumptions,
                        &left_truthiness.facts,
                        &left_truthiness.obligations,
                    );
                    for right_path in
                        evaluate_c_expression_paths(state, right, &right_assumptions, budget)?
                    {
                        let Some((facts, obligations)) = merge_path_facts_and_obligations(
                            &left_truthiness.facts,
                            &left_truthiness.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                        ) else {
                            continue;
                        };

                        match right_path.outcome {
                            CExpressionOutcome::Value(value) => {
                                paths.extend(c_truthiness_as_c_int32_paths(
                                    value,
                                    facts,
                                    obligations,
                                    assumptions,
                                ))
                            }
                            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => paths
                                .push(CExpressionPath {
                                    outcome: CExpressionOutcome::UndefinedBehavior(
                                        undefined_behavior,
                                    ),
                                    facts,
                                    obligations,
                                }),
                            CExpressionOutcome::RuntimeError(error) => {
                                paths.push(CExpressionPath {
                                    outcome: CExpressionOutcome::RuntimeError(error),
                                    facts,
                                    obligations,
                                })
                            }
                        }
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_path.facts,
                    obligations: left_path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: left_path.facts,
                obligations: left_path.obligations,
            }),
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn evaluate_c_logical_or_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        match left_path.outcome {
            CExpressionOutcome::Value(left_value) => {
                for left_truthiness in c_truthiness_paths(
                    left_value,
                    left_path.facts,
                    left_path.obligations,
                    assumptions,
                ) {
                    if left_truthiness.is_true {
                        paths.push(CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(1)),
                            facts: left_truthiness.facts,
                            obligations: left_truthiness.obligations,
                        });
                        continue;
                    }

                    let right_assumptions = assumptions_with_path_context(
                        assumptions,
                        &left_truthiness.facts,
                        &left_truthiness.obligations,
                    );
                    for right_path in
                        evaluate_c_expression_paths(state, right, &right_assumptions, budget)?
                    {
                        let Some((facts, obligations)) = merge_path_facts_and_obligations(
                            &left_truthiness.facts,
                            &left_truthiness.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                        ) else {
                            continue;
                        };

                        match right_path.outcome {
                            CExpressionOutcome::Value(value) => {
                                paths.extend(c_truthiness_as_c_int32_paths(
                                    value,
                                    facts,
                                    obligations,
                                    assumptions,
                                ))
                            }
                            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => paths
                                .push(CExpressionPath {
                                    outcome: CExpressionOutcome::UndefinedBehavior(
                                        undefined_behavior,
                                    ),
                                    facts,
                                    obligations,
                                }),
                            CExpressionOutcome::RuntimeError(error) => {
                                paths.push(CExpressionPath {
                                    outcome: CExpressionOutcome::RuntimeError(error),
                                    facts,
                                    obligations,
                                })
                            }
                        }
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_path.facts,
                    obligations: left_path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: left_path.facts,
                obligations: left_path.obligations,
            }),
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn pointer_equality_condition(left: Pointer, right: Pointer) -> ConditionTerm {
    if left.block != right.block {
        ConditionTerm::Constant(false)
    } else {
        ConditionTerm::pointer_offset_equal(left.offset, right.offset)
    }
}

fn pointer_is_null_condition(pointer: Pointer) -> ConditionTerm {
    pointer_equality_condition(
        pointer,
        Pointer {
            block: "null".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        },
    )
}

fn evaluate_c_int32_binary_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
    apply: impl Fn(
        Bitvector32Term,
        Bitvector32Term,
        Vec<PathFact>,
        Vec<ProofObligation>,
    ) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(CValue::Int32(left)) => left,
            CExpressionOutcome::Value(_) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExpressionOutcome::Value(CValue::Int32(right)) => {
                    paths.extend(apply(left.clone(), right, facts, obligations));
                }
                CExpressionOutcome::Value(_) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts,
                    obligations,
                }),
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_statement(
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
) -> Option<CStatementOutcome> {
    let paths = execute_c_statement_paths(
        state,
        statement,
        assumptions,
        &CFunctionEnvironment::new(),
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.outcome)
}

fn execute_c_lvalue_assignment_paths(
    state: &CState,
    target: &CExpression,
    value: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    for target_path in evaluate_c_lvalue_paths(state, target, assumptions, budget)? {
        let CLValuePath {
            outcome: target_outcome,
            facts: target_facts,
            obligations: target_obligations,
        } = target_path;

        let target_lvalue = match target_outcome {
            CLValueOutcome::LValue(lvalue) => lvalue,
            CLValueOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts: target_facts,
                    obligations: target_obligations,
                });
                continue;
            }
            CLValueOutcome::RuntimeError(error) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(error),
                    facts: target_facts,
                    obligations: target_obligations,
                });
                continue;
            }
        };

        let value_assumptions =
            assumptions_with_path_context(assumptions, &target_facts, &target_obligations);
        for value_path in evaluate_c_expression_paths(state, value, &value_assumptions, budget)? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &target_facts,
                &target_obligations,
                &value_path.facts,
                &value_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match value_path.outcome {
                CExpressionOutcome::Value(value) => paths.extend(write_c_lvalue_paths(
                    state,
                    target_lvalue.clone(),
                    value,
                    facts,
                    obligations,
                    assumptions,
                )),
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CStatementExecutionPath {
                        outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn write_c_lvalue_paths(
    state: &CState,
    lvalue: CLValue,
    value: CValue,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CStatementExecutionPath> {
    if !lvalue.value_type.accepts(&value) {
        return vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }];
    }

    match lvalue.storage {
        CLValueStorage::Local { name } => {
            let mut state = state.clone();
            sync_stack_local(&mut state, &name, &value);
            state.locals.set(name, value);
            vec![CStatementExecutionPath {
                outcome: CStatementOutcome::Normal(state),
                facts,
                obligations,
            }]
        }
        CLValueStorage::Memory { pointer } => {
            let Some(obligations) = add_memory_store_obligation(
                &state.memory,
                &pointer,
                &value,
                obligations,
                assumptions,
            ) else {
                return Vec::new();
            };
            let before_memory = state.memory.clone();
            let mut state = state.clone();
            state.memory = state
                .memory
                .without_possible_aliasing_cells(&pointer, assumptions)
                .store(pointer.clone(), value.clone());
            let mut facts = facts;
            if add_internal_path_fact(
                &mut facts,
                assumptions,
                Proposition::CMemoryMutatesOnly {
                    before: before_memory,
                    after: state.memory.clone(),
                    pointers: vec![pointer.clone()],
                },
            )
            .is_none()
            {
                return Vec::new();
            }
            if let Some(name) = local_name_from_pointer(&pointer) {
                if state.locals.get(name).is_some() {
                    state.locals.set(name.to_string(), value);
                }
            }
            vec![CStatementExecutionPath {
                outcome: CStatementOutcome::Normal(state),
                facts,
                obligations,
            }]
        }
    }
}

fn local_name_from_pointer(pointer: &Pointer) -> Option<&str> {
    if pointer.offset != PointerOffsetTerm::Constant(0) {
        return None;
    }
    pointer.block.strip_prefix("local:")
}

fn execute_c_statement_paths(
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    budget.consume_statement_step()?;
    let paths = match statement {
        CStatement::Declare { name, c_type } => vec![CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(declare_local(state, name, *c_type)),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CStatement::Assign { name, expression } => execute_c_lvalue_assignment_paths(
            state,
            &c_variable(name.clone()),
            expression,
            assumptions,
            budget,
        )?,
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => execute_c_call_assign_paths(
            state,
            target,
            function_name,
            arguments,
            assumptions,
            environment,
            budget,
        )?,
        CStatement::Assert { condition, label } => {
            execute_c_assert_paths(state, condition, label.as_deref(), assumptions, budget)?
        }
        CStatement::Seq(first, second) => {
            let mut paths = Vec::new();
            for first_path in
                execute_c_statement_paths(state, first, assumptions, environment, budget)?
            {
                match first_path.outcome {
                    CStatementOutcome::Normal(state) => {
                        paths.extend(execute_c_statement_paths_with_prefix(
                            &state,
                            second,
                            assumptions,
                            environment,
                            &first_path.facts,
                            &first_path.obligations,
                            budget,
                        )?);
                    }
                    outcome @ (CStatementOutcome::Return { .. }
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                        outcome,
                        facts: first_path.facts,
                        obligations: first_path.obligations,
                    }),
                }
            }
            paths
        }
        CStatement::Return(expression) => {
            evaluate_c_expression_paths(state, expression, assumptions, budget)?
                .into_iter()
                .map(|path| CStatementExecutionPath {
                    outcome: match path.outcome {
                        CExpressionOutcome::Value(value) => CStatementOutcome::Return {
                            value,
                            state: state.clone(),
                        },
                        CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                            CStatementOutcome::UndefinedBehavior(undefined_behavior)
                        }
                        CExpressionOutcome::RuntimeError(error) => {
                            CStatementOutcome::RuntimeError(error)
                        }
                    },
                    facts: path.facts,
                    obligations: path.obligations,
                })
                .collect()
        }
        CStatement::Store { pointer, value } => execute_c_lvalue_assignment_paths(
            state,
            &CExpression::Load(Box::new(pointer.clone())),
            value,
            assumptions,
            budget,
        )?,
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut paths = Vec::new();
            for condition_path in
                evaluate_c_expression_paths(state, condition, assumptions, budget)?
            {
                let CExpressionPath {
                    outcome,
                    facts,
                    obligations,
                } = condition_path;
                match outcome {
                    CExpressionOutcome::Value(value) => {
                        let truthiness_paths =
                            c_truthiness_paths(value, facts, obligations, assumptions);
                        for truthiness_path in truthiness_paths {
                            let branch = if truthiness_path.is_true {
                                then_branch
                            } else {
                                else_branch
                            };
                            paths.extend(execute_c_statement_paths_with_prefix(
                                state,
                                branch,
                                assumptions,
                                environment,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                                budget,
                            )?);
                        }
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        })
                    }
                }
            }
            paths
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks: _,
            effect_checks: _,
            body,
        } => execute_c_while_paths(
            state,
            condition,
            invariant,
            body,
            assumptions,
            environment,
            budget,
        )?,
    };
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_assert_paths(
    state: &CState,
    condition: &CExpression,
    label: Option<&str>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    for condition_path in evaluate_c_expression_paths(state, condition, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        match outcome {
            CExpressionOutcome::Value(value) => {
                let assertion_obligation = assertion_truthiness_obligation(&value, label);
                for truthiness_path in c_truthiness_paths(value, facts, obligations, assumptions) {
                    let mut obligations = truthiness_path.obligations;
                    if !truthiness_path.is_true {
                        obligations.push(assertion_obligation.clone());
                    }
                    paths.push(CStatementExecutionPath {
                        outcome: CStatementOutcome::Normal(state.clone()),
                        facts: truthiness_path.facts,
                        obligations,
                    });
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts,
                    obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(error),
                facts,
                obligations,
            }),
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn assertion_truthiness_obligation(value: &CValue, label: Option<&str>) -> ProofObligation {
    let obligation = ProofObligation::verification_condition(Proposition::Equal(
        Term::CValue(value.clone()),
        Term::CValue(int32(1)),
    ));
    match label {
        Some(label) => obligation.with_context(label),
        None => obligation,
    }
}

fn execute_c_while_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    body: &CStatement,
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    budget.consume_loop_unroll()?;

    let mut base_obligations = Vec::new();
    for proposition in invariant {
        if add_proof_obligation(&mut base_obligations, assumptions, proposition.clone()).is_none() {
            return Ok(Vec::new());
        }
    }
    let loop_assumptions = assumptions_with_propositions(assumptions, invariant);
    let mut paths = Vec::new();

    for condition_path in evaluate_c_expression_paths(state, condition, &loop_assumptions, budget)?
    {
        let Some((condition_facts, condition_obligations)) = merge_path_facts_and_obligations(
            &[],
            &base_obligations,
            &condition_path.facts,
            &condition_path.obligations,
            assumptions,
        ) else {
            continue;
        };

        match condition_path.outcome {
            CExpressionOutcome::Value(value) => {
                let truthiness_paths =
                    c_truthiness_paths(value, condition_facts, condition_obligations, assumptions);
                for truthiness_path in truthiness_paths {
                    if truthiness_path.is_true {
                        paths.extend(execute_c_while_body_paths(
                            state,
                            condition,
                            invariant,
                            body,
                            assumptions,
                            environment,
                            truthiness_path.facts,
                            truthiness_path.obligations,
                            budget,
                        )?);
                    } else {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::Normal(state.clone()),
                            facts: truthiness_path.facts,
                            obligations: truthiness_path.obligations,
                        });
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts: condition_facts,
                    obligations: condition_obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(error),
                facts: condition_facts,
                obligations: condition_obligations,
            }),
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_while_body_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    body: &CStatement,
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    facts: Vec<PathFact>,
    obligations: Vec<ProofObligation>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let body_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    let mut paths = Vec::new();
    for body_path in execute_c_statement_paths(state, body, &body_assumptions, environment, budget)?
    {
        let Some((facts, obligations)) = merge_path_facts_and_obligations(
            &facts,
            &obligations,
            &body_path.facts,
            &body_path.obligations,
            assumptions,
        ) else {
            continue;
        };

        match body_path.outcome {
            CStatementOutcome::Normal(next_state) => {
                let next_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                for path in execute_c_while_paths(
                    &next_state,
                    condition,
                    invariant,
                    body,
                    &next_assumptions,
                    environment,
                    budget,
                )? {
                    let (facts, obligations) = merge_path_facts_and_obligations(
                        &facts,
                        &obligations,
                        &path.facts,
                        &path.obligations,
                        assumptions,
                    )
                    .expect("merged loop path facts should remain consistent");
                    paths.push(CStatementExecutionPath {
                        outcome: path.outcome,
                        facts,
                        obligations,
                    });
                }
            }
            outcome @ (CStatementOutcome::Return { .. }
            | CStatementOutcome::UndefinedBehavior(_)
            | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                outcome,
                facts,
                obligations,
            }),
        }
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn declare_local(state: &CState, name: &str, c_type: CType) -> CState {
    let mut state = state.clone();
    let (initial_value, byte_width) = match c_type {
        CType::Int32 => (int32(0), 4),
        CType::Int32Pointer => (
            CValue::Pointer(Pointer {
                block: "null".to_string(),
                offset: PointerOffsetTerm::Constant(0),
            }),
            C_POINTER_BYTE_WIDTH,
        ),
        CType::Int32Array(length) => {
            let pointer = CMemory::local_pointer(name);
            state.memory = state
                .memory
                .with_block(pointer.block, length.checked_mul(4).unwrap_or(u32::MAX));
            state
                .locals
                .set_array_object(name.to_string(), CType::Int32, length);
            return state;
        }
    };
    let pointer = CMemory::local_pointer(name);
    state.memory = state
        .memory
        .with_block(pointer.block.clone(), byte_width)
        .store(pointer, initial_value.clone());
    state.locals.set(name.to_string(), initial_value);
    state
}

fn sync_stack_local(state: &mut CState, name: &str, value: &CValue) {
    let pointer = CMemory::local_pointer(name);
    if state.memory.has_block(&pointer.block) {
        state.memory = state.memory.clone().store(pointer, value.clone());
    }
}

fn execute_c_call_assign_paths(
    state: &CState,
    target: &str,
    function_name: &str,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let Some(function) = environment.get_function(function_name) else {
        return Ok(vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    };

    let paths =
        execute_c_function_paths(state, function, arguments, assumptions, environment, budget)?
            .into_iter()
            .map(|path| {
                let outcome = match path.outcome {
                    CFunctionOutcome::Return { value, mut state } => {
                        if state.locals.is_array_object(target) {
                            return CStatementExecutionPath {
                                outcome: CStatementOutcome::RuntimeError(
                                    CRuntimeError::TypeMismatch,
                                ),
                                facts: path.facts,
                                obligations: path.obligations,
                            };
                        }
                        sync_stack_local(&mut state, target, &value);
                        state.locals.set(target.to_string(), value);
                        CStatementOutcome::Normal(state)
                    }
                    CFunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                        CStatementOutcome::UndefinedBehavior(undefined_behavior)
                    }
                    CFunctionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                };

                CStatementExecutionPath {
                    outcome,
                    facts: path.facts,
                    obligations: path.obligations,
                }
            })
            .collect::<Vec<_>>();
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_statement_paths_with_prefix(
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    prefix_facts: &[PathFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let paths = execute_c_statement_paths(
        state,
        statement,
        &effective_assumptions,
        environment,
        budget,
    )?
    .into_iter()
    .filter_map(|path| {
        let (facts, obligations) = merge_path_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &path.facts,
            &path.obligations,
            assumptions,
        )?;
        Some(CStatementExecutionPath {
            outcome: path.outcome,
            facts,
            obligations,
        })
    })
    .collect::<Vec<_>>();
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_statement_verification_paths(
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
    variables: &mut VerificationVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    budget.consume_statement_step()?;
    let paths = match statement {
        CStatement::Seq(first, second) => {
            let mut paths = Vec::new();
            for first_path in execute_c_statement_verification_paths(
                state,
                first,
                assumptions,
                environment,
                budget,
                variables,
            )? {
                match first_path.outcome {
                    CStatementOutcome::Normal(state) => {
                        paths.extend(execute_c_statement_verification_paths_with_prefix(
                            &state,
                            second,
                            assumptions,
                            environment,
                            &first_path.facts,
                            &first_path.obligations,
                            budget,
                            variables,
                        )?);
                    }
                    outcome @ (CStatementOutcome::Return { .. }
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                        outcome,
                        facts: first_path.facts,
                        obligations: first_path.obligations,
                    }),
                }
            }
            paths
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut paths = Vec::new();
            for condition_path in
                evaluate_c_expression_paths(state, condition, assumptions, budget)?
            {
                let CExpressionPath {
                    outcome,
                    facts,
                    obligations,
                } = condition_path;
                match outcome {
                    CExpressionOutcome::Value(value) => {
                        for truthiness_path in
                            c_truthiness_paths(value, facts, obligations, assumptions)
                        {
                            let branch = if truthiness_path.is_true {
                                then_branch
                            } else {
                                else_branch
                            };
                            paths.extend(execute_c_statement_verification_paths_with_prefix(
                                state,
                                branch,
                                assumptions,
                                environment,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                                budget,
                                variables,
                            )?);
                        }
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        })
                    }
                }
            }
            paths
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
        } if !invariant_checks.is_empty() || !effect_checks.is_empty() => {
            execute_c_while_verification_paths(
                state,
                condition,
                invariant,
                invariant_checks,
                effect_checks,
                body,
                assumptions,
                environment,
                budget,
                variables,
            )?
        }
        _ => execute_c_statement_paths(state, statement, assumptions, environment, budget)?,
    };
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_statement_verification_paths_with_prefix(
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    prefix_facts: &[PathFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
    variables: &mut VerificationVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let paths = execute_c_statement_verification_paths(
        state,
        statement,
        &effective_assumptions,
        environment,
        budget,
        variables,
    )?
    .into_iter()
    .filter_map(|path| {
        let (facts, obligations) = merge_path_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &path.facts,
            &path.obligations,
            assumptions,
        )?;
        Some(CStatementExecutionPath {
            outcome: path.outcome,
            facts,
            obligations,
        })
    })
    .collect::<Vec<_>>();
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_while_verification_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
    variables: &mut VerificationVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut base_obligations = Vec::new();
    for proposition in invariant {
        if add_proof_obligation(&mut base_obligations, assumptions, proposition.clone()).is_none() {
            return Ok(Vec::new());
        }
    }

    let entry_obligations = collect_invariant_check_obligations(
        state,
        invariant_checks,
        InvariantPhase::Entry,
        assumptions,
        budget,
    )?;
    let top_state = havoc_loop_modified_locals(state, body, variables);
    let whole_loop_effect_summaries = collect_whole_loop_effect_summaries(
        state,
        &top_state,
        effect_checks,
        statement_may_write_memory(body),
        assumptions,
        budget,
    )?;
    let preservation_summary = collect_loop_preservation_summary(
        &top_state,
        condition,
        invariant_checks,
        effect_checks,
        &whole_loop_effect_summaries,
        body,
        assumptions,
        environment,
        budget,
        variables,
    )?;
    let mut loop_check_obligations = Vec::new();
    append_required_proof_obligations(&mut loop_check_obligations, assumptions, &entry_obligations);
    append_required_proof_obligations(
        &mut loop_check_obligations,
        assumptions,
        &preservation_summary.obligations,
    );

    let mut paths = Vec::new();
    for (invariant_facts, invariant_obligations) in assume_invariant_checks(
        &top_state,
        invariant_checks,
        assumptions,
        &[],
        &base_obligations,
        budget,
    )? {
        for (mut facts, mut obligations) in assume_condition_truthiness(
            &top_state,
            condition,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            false,
            budget,
        )? {
            for summary in &whole_loop_effect_summaries {
                let _ = add_path_fact(&mut facts, assumptions, summary.clone());
            }
            append_required_proof_obligations(
                &mut obligations,
                assumptions,
                &loop_check_obligations,
            );
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::Normal(top_state.clone()),
                facts,
                obligations,
            });
        }
    }
    if paths.is_empty() {
        let mut obligations = base_obligations;
        append_required_proof_obligations(&mut obligations, assumptions, &loop_check_obligations);
        obligations.push(
            ProofObligation::verification_condition(false_equals_true_proposition())
                .with_context("loop exit reachability"),
        );
        paths.push(CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(top_state.clone()),
            facts: Vec::new(),
            obligations,
        });
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InvariantPhase {
    Entry,
    Preservation,
}

fn invariant_context(check: &CLoopInvariantCheck, phase: InvariantPhase) -> Option<&str> {
    match phase {
        InvariantPhase::Entry => check.entry_context(),
        InvariantPhase::Preservation => check.preservation_context(),
    }
}

fn collect_invariant_check_obligations(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    phase: InvariantPhase,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    let mut contexts = vec![(Vec::new(), Vec::new())];
    let mut all_obligations = Vec::new();
    for check in invariant_checks {
        let mut next_contexts = Vec::new();
        for (facts, obligations) in contexts {
            let effective_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            for path in lower_c_proposition_at_state(
                state,
                check.proposition(),
                &effective_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_path_facts_and_obligations(
                    &facts,
                    &obligations,
                    &path.facts,
                    &path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                let mut obligations = obligations;
                let obligation_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let proposition = wrap_path_context(path.proposition, &facts, &obligations);
                add_required_proof_obligation_with_context(
                    &mut obligations,
                    &obligation_assumptions,
                    proposition,
                    invariant_context(check, phase),
                );
                append_required_proof_obligations(&mut all_obligations, assumptions, &obligations);
                next_contexts.push((facts, obligations));
            }
        }
        contexts = next_contexts;
    }
    Ok(all_obligations)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LoopPreservationSummary {
    obligations: Vec<ProofObligation>,
}

fn collect_loop_preservation_summary(
    top_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    whole_loop_effect_summaries: &[Proposition],
    body: &CStatement,
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
    variables: &mut VerificationVariableGenerator,
) -> ExecutionResult<LoopPreservationSummary> {
    let mut obligations = Vec::new();
    for (mut invariant_facts, invariant_obligations) in
        assume_invariant_checks(top_state, invariant_checks, assumptions, &[], &[], budget)?
    {
        for summary in whole_loop_effect_summaries {
            let _ = add_path_fact(&mut invariant_facts, assumptions, summary.clone());
        }
        for (condition_facts, condition_obligations) in assume_condition_truthiness(
            top_state,
            condition,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            true,
            budget,
        )? {
            for body_path in execute_c_statement_verification_paths_with_prefix(
                top_state,
                body,
                assumptions,
                environment,
                &condition_facts,
                &condition_obligations,
                budget,
                variables,
            )? {
                match body_path.outcome {
                    CStatementOutcome::Normal(next_state) => {
                        let effect_obligations = collect_loop_effect_check_obligations(
                            top_state,
                            &next_state,
                            effect_checks,
                            &body_path.facts,
                            &body_path.obligations,
                            assumptions,
                            budget,
                        )?;
                        let path_obligations = collect_invariant_check_obligations(
                            &next_state,
                            invariant_checks,
                            InvariantPhase::Preservation,
                            &assumptions_with_path_context(
                                assumptions,
                                &body_path.facts,
                                &body_path.obligations,
                            ),
                            budget,
                        )?;
                        append_required_proof_obligations(
                            &mut obligations,
                            assumptions,
                            &body_path.obligations,
                        );
                        append_required_proof_obligations_under_path_context(
                            &mut obligations,
                            assumptions,
                            &effect_obligations,
                            &body_path.facts,
                            &body_path.obligations,
                        );
                        append_required_proof_obligations_under_path_context(
                            &mut obligations,
                            assumptions,
                            &path_obligations,
                            &body_path.facts,
                            &body_path.obligations,
                        );
                    }
                    CStatementOutcome::Return { .. }
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_) => {
                        let mut path_obligations = body_path.obligations;
                        path_obligations.push(
                            ProofObligation::verification_condition(false_equals_true_proposition())
                                .with_context("loop preservation body safety"),
                        );
                        append_required_proof_obligations(
                            &mut obligations,
                            assumptions,
                            &path_obligations,
                        );
                    }
                }
            }
        }
    }
    Ok(LoopPreservationSummary { obligations })
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct EvaluatedMemorySegment {
    base: Pointer,
    start: Bitvector32Term,
    end: Bitvector32Term,
}

fn collect_whole_loop_effect_summaries(
    before_state: &CState,
    after_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    include_mutable_summaries: bool,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<Proposition>> {
    let mut summaries = Vec::new();
    for check in effect_checks {
        if check.span() != CLoopEffectSpan::Whole {
            continue;
        }

        let ranges = match check.effect() {
            CLoopEffect::Immutable => Vec::new(),
            // A mutable clause is an upper bound. Without a memory-writing
            // body, it is not evidence of mutation and should not block an
            // enclosing immutable claim.
            CLoopEffect::Mutable(_) if !include_mutable_summaries => continue,
            CLoopEffect::Mutable(segments) => {
                let mut ranges = Vec::new();
                let mut failed = false;
                for segment in segments {
                    match evaluate_loop_effect_segment(before_state, segment, assumptions, budget)?
                    {
                        Ok(segment) => {
                            ranges.push(CMemoryRange::new(segment.base, segment.start, segment.end))
                        }
                        Err(_) => {
                            failed = true;
                            break;
                        }
                    }
                }
                if failed {
                    continue;
                }
                ranges
            }
        };

        summaries.push(Proposition::CMemoryEffectSummary {
            before: before_state.memory().clone(),
            after: after_state.memory().clone(),
            mutable_ranges: ranges,
        });
    }
    Ok(summaries)
}

fn collect_loop_effect_check_obligations(
    before_state: &CState,
    after_state: &CState,
    effect_checks: &[CLoopEffectCheck],
    facts: &[PathFact],
    path_obligations: &[ProofObligation],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    if effect_checks.is_empty() {
        return Ok(Vec::new());
    }

    let effective_assumptions = assumptions_with_path_context(assumptions, facts, path_obligations);
    let mut writes = after_state
        .memory()
        .differing_cell_pointers(before_state.memory())
        .into_iter()
        .filter(is_loop_effect_relevant_pointer)
        .collect::<BTreeSet<_>>();
    writes.extend(
        facts
            .iter()
            .filter_map(|fact| match fact.proposition() {
                Proposition::CMemoryMutatesOnly { pointers, .. } => Some(pointers.as_slice()),
                _ => None,
            })
            .flatten()
            .cloned(),
    );
    writes.retain(is_loop_effect_relevant_pointer);

    let mut obligations = Vec::new();
    for check in effect_checks {
        let mut segment_evaluation_failed = false;
        let segments = match check.effect() {
            CLoopEffect::Immutable => Vec::new(),
            CLoopEffect::Mutable(segments) => {
                let mut evaluated = Vec::new();
                for (segment_index, segment) in segments.iter().enumerate() {
                    match evaluate_loop_effect_segment(
                        before_state,
                        segment,
                        &effective_assumptions,
                        budget,
                    )? {
                        Ok(segment) => evaluated.push(segment),
                        Err(message) => {
                            segment_evaluation_failed = true;
                            push_false_loop_effect_obligation(
                                &mut obligations,
                                loop_effect_failure_context(
                                    check,
                                    format!(
                                        "could not evaluate mutable segment {segment_index} in {:?}: {message}",
                                        check.effect()
                                    ),
                                ),
                            );
                        }
                    }
                }
                evaluated
            }
        };

        if segment_evaluation_failed {
            continue;
        }

        for pointer in &writes {
            if !segments.iter().any(|segment| {
                loop_effect_segment_contains_pointer(segment, pointer, &effective_assumptions)
            }) {
                push_false_loop_effect_obligation(
                    &mut obligations,
                    loop_effect_failure_context(
                        check,
                        format!(
                            "write to {pointer:?} is outside the mutable footprint; external writes: {writes:?}; declared effect: {:?}; evaluated segments: {segments:?}",
                            check.effect()
                        ),
                    ),
                );
            }
        }
    }

    Ok(obligations)
}

fn evaluate_loop_effect_segment(
    state: &CState,
    segment: &CMemorySegment,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<EvaluatedMemorySegment, String>> {
    let base = match evaluate_loop_effect_segment_value(
        state,
        &segment.base,
        assumptions,
        "segment base",
        budget,
    )? {
        Ok(CValue::Pointer(pointer)) => pointer,
        Ok(value) => {
            return Ok(Err(format!(
                "segment base evaluated to {value:?}, not pointer"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let start = match evaluate_loop_effect_segment_value(
        state,
        &segment.start,
        assumptions,
        "segment start",
        budget,
    )? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment start evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };
    let end = match evaluate_loop_effect_segment_value(
        state,
        &segment.end,
        assumptions,
        "segment end",
        budget,
    )? {
        Ok(CValue::Int32(value)) => value,
        Ok(value) => {
            return Ok(Err(format!(
                "segment end evaluated to {value:?}, not int32"
            )));
        }
        Err(message) => return Ok(Err(message)),
    };

    Ok(Ok(EvaluatedMemorySegment { base, start, end }))
}

fn evaluate_loop_effect_segment_value(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
    label: &str,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CValue, String>> {
    let paths = evaluate_c_expression_paths(state, expression, assumptions, budget)?;
    if paths.len() != 1 {
        return Ok(Err(format!(
            "{label} evaluated through {} paths, expected exactly one",
            paths.len()
        )));
    }
    let Some(path) = paths.into_iter().next() else {
        return Ok(Err(format!("{label} had no evaluation path")));
    };
    if !path.obligations.is_empty() {
        return Ok(Err(format!(
            "{label} left proof obligations: {:?}",
            path.obligations
        )));
    }
    match path.outcome {
        CExpressionOutcome::Value(value) => Ok(Ok(value)),
        CExpressionOutcome::UndefinedBehavior(undefined_behavior) => Ok(Err(format!(
            "{label} produced undefined behavior: {undefined_behavior:?}"
        ))),
        CExpressionOutcome::RuntimeError(error) => {
            Ok(Err(format!("{label} produced runtime error: {error:?}")))
        }
    }
}

fn loop_effect_segment_contains_pointer(
    segment: &EvaluatedMemorySegment,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    let Some(index) = pointer.element_index_from_base(&segment.base) else {
        return false;
    };
    assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(segment.start.clone(), index.clone()),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_than(index, segment.end.clone()),
        true,
    ))
}

fn is_loop_effect_relevant_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
}

fn loop_effect_failure_context(check: &CLoopEffectCheck, message: String) -> String {
    match check.context() {
        Some(context) => format!("{context}: {message}"),
        None => message,
    }
}

fn push_false_loop_effect_obligation(obligations: &mut Vec<ProofObligation>, context: String) {
    obligations.push(
        ProofObligation::verification_condition(false_equals_true_proposition())
            .with_context(context),
    );
}

fn false_equals_true_proposition() -> Proposition {
    Proposition::Equal(
        Term::Condition(ConditionTerm::Constant(false)),
        Term::Condition(ConditionTerm::Constant(true)),
    )
}

fn assume_invariant_checks(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
    prefix_facts: &[PathFact],
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<(Vec<PathFact>, Vec<ProofObligation>)>> {
    let mut contexts = vec![(prefix_facts.to_vec(), prefix_obligations.to_vec())];
    for check in invariant_checks {
        let mut next_contexts = Vec::new();
        for (facts, obligations) in contexts {
            let effective_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            for path in lower_c_proposition_at_state(
                state,
                check.proposition(),
                &effective_assumptions,
                budget,
            )? {
                let Some((mut facts, obligations)) = merge_path_facts_and_obligations(
                    &facts,
                    &obligations,
                    &path.facts,
                    &path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                if add_path_fact(&mut facts, assumptions, path.proposition).is_some() {
                    next_contexts.push((facts, obligations));
                }
            }
        }
        contexts = next_contexts;
    }
    Ok(contexts)
}

fn assume_condition_truthiness(
    state: &CState,
    condition: &CExpression,
    assumptions: &Assumptions,
    prefix_facts: &[PathFact],
    prefix_obligations: &[ProofObligation],
    desired_truthiness: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<(Vec<PathFact>, Vec<ProofObligation>)>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let mut contexts = Vec::new();
    for condition_path in
        evaluate_c_expression_paths(state, condition, &effective_assumptions, budget)?
    {
        let Some((facts, obligations)) = merge_path_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &condition_path.facts,
            &condition_path.obligations,
            assumptions,
        ) else {
            continue;
        };
        let CExpressionOutcome::Value(value) = condition_path.outcome else {
            continue;
        };
        for truthiness_path in c_truthiness_paths(value, facts, obligations, assumptions) {
            if truthiness_path.is_true == desired_truthiness {
                contexts.push((truthiness_path.facts, truthiness_path.obligations));
            }
        }
    }
    Ok(contexts)
}

fn havoc_loop_modified_locals(
    state: &CState,
    body: &CStatement,
    variables: &mut VerificationVariableGenerator,
) -> CState {
    let mut state = state.clone();
    let mut names = BTreeSet::new();
    collect_loop_modified_locals(body, &mut names);
    for name in names {
        let Some(binding) = state.locals.binding(&name) else {
            continue;
        };
        let CLocalBinding::Object(value) = binding else {
            continue;
        };
        let value = match value.c_type() {
            CType::Int32 => int32(Bitvector32Term::Variable(variables.next())),
            CType::Int32Pointer => continue,
            CType::Int32Array(_) => continue,
        };
        sync_stack_local(&mut state, &name, &value);
        state.locals.set(name, value);
    }
    if statement_may_write_memory(body) {
        state.memory = state.memory.with_havoc_marker(variables.next());
    }
    state
}

fn statement_may_write_memory(statement: &CStatement) -> bool {
    match statement {
        CStatement::Declare { .. }
        | CStatement::Assign { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_) => false,
        CStatement::CallAssign { .. } | CStatement::Store { .. } => true,
        CStatement::Seq(first, second) => {
            statement_may_write_memory(first) || statement_may_write_memory(second)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => statement_may_write_memory(then_branch) || statement_may_write_memory(else_branch),
        CStatement::While { body, .. } => statement_may_write_memory(body),
    }
}

fn collect_loop_modified_locals(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Declare { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. } => {}
        CStatement::Assign { name, .. } => {
            names.insert(name.clone());
        }
        CStatement::CallAssign { target, .. } => {
            names.insert(target.clone());
        }
        CStatement::Seq(first, second) => {
            collect_loop_modified_locals(first, names);
            collect_loop_modified_locals(second, names);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loop_modified_locals(then_branch, names);
            collect_loop_modified_locals(else_branch, names);
        }
        CStatement::While { body, .. } => {
            collect_loop_modified_locals(body, names);
        }
    }
}

fn execute_c_function_paths(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    budget.consume_function_call()?;
    if arguments.len() != function.parameters.len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters.len(),
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }

    let mut paths = Vec::new();
    for arguments_path in evaluate_c_arguments_paths(caller_state, arguments, assumptions, budget)?
    {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }

        let Some(callee_state) =
            bind_c_function_arguments(caller_state, function, &arguments_path.values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        for body_path in execute_c_statement_paths(
            &callee_state,
            function.body(),
            &body_assumptions,
            environment,
            budget,
        )? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &arguments_path.facts,
                &arguments_path.obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            paths.push(CFunctionPath {
                outcome: function_outcome_from_body(caller_state, function, body_path.outcome),
                facts,
                obligations,
            });
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn execute_c_function_verification_paths(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    environment: &CFunctionEnvironment,
    budget: &mut ExecutionBudget,
    variables: &mut VerificationVariableGenerator,
) -> ExecutionResult<Vec<CFunctionPath>> {
    budget.consume_function_call()?;
    if arguments.len() != function.parameters.len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters.len(),
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }

    let mut paths = Vec::new();
    for arguments_path in evaluate_c_arguments_paths(caller_state, arguments, assumptions, budget)?
    {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        }

        let Some(callee_state) =
            bind_c_function_arguments(caller_state, function, &arguments_path.values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        for body_path in execute_c_statement_verification_paths(
            &callee_state,
            function.body(),
            &body_assumptions,
            environment,
            budget,
            variables,
        )? {
            let Some((facts, obligations)) = merge_path_facts_and_obligations(
                &arguments_path.facts,
                &arguments_path.obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            paths.push(CFunctionPath {
                outcome: function_outcome_from_body(caller_state, function, body_path.outcome),
                facts,
                obligations,
            });
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn add_memory_store_obligation(
    memory: &CMemory,
    pointer: &Pointer,
    value: &CValue,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Option<Vec<ProofObligation>> {
    if memory.can_store_concretely(pointer, value) {
        return Some(obligations);
    }

    add_proof_obligation(
        &mut obligations,
        assumptions,
        Proposition::CMemoryCanStore {
            memory: memory.clone(),
            pointer: pointer.clone(),
        },
    )?;
    Some(obligations)
}

fn evaluate_c_arguments_paths(
    state: &CState,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CArgumentsPath>> {
    let mut paths = vec![CArgumentsPath {
        values: Vec::new(),
        outcome: None,
        facts: Vec::new(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let mut next_paths = Vec::new();
        for path in paths {
            if path.outcome.is_some() {
                next_paths.push(path);
                continue;
            }

            let argument_assumptions =
                assumptions_with_path_context(assumptions, &path.facts, &path.obligations);
            for argument_path in
                evaluate_c_expression_paths(state, argument, &argument_assumptions, budget)?
            {
                let Some((facts, obligations)) = merge_path_facts_and_obligations(
                    &path.facts,
                    &path.obligations,
                    &argument_path.facts,
                    &argument_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };

                match argument_path.outcome {
                    CExpressionOutcome::Value(value) => {
                        let mut values = path.values.clone();
                        values.push(value);
                        next_paths.push(CArgumentsPath {
                            values,
                            outcome: None,
                            facts,
                            obligations,
                        });
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        next_paths.push(CArgumentsPath {
                            values: path.values.clone(),
                            outcome: Some(CFunctionOutcome::UndefinedBehavior(undefined_behavior)),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => next_paths.push(CArgumentsPath {
                        values: path.values.clone(),
                        outcome: Some(CFunctionOutcome::RuntimeError(error)),
                        facts,
                        obligations,
                    }),
                }
            }
        }
        budget.consume_paths(next_paths.len())?;
        paths = next_paths;
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

fn bind_c_function_arguments(
    caller_state: &CState,
    function: &CFunction,
    values: &[CValue],
) -> Option<CState> {
    let mut callee_state = CState::new().with_memory(caller_state.memory.clone());
    for (parameter, value) in function.parameters().iter().zip(values) {
        if !parameter.c_type().accepts(value) {
            return None;
        }
        callee_state
            .locals
            .set(parameter.name().to_string(), value.clone());
    }
    Some(callee_state)
}

fn function_outcome_from_body(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
) -> CFunctionOutcome {
    match outcome {
        CStatementOutcome::Return { value, state } => {
            if !function.return_type().accepts(&value) {
                return CFunctionOutcome::RuntimeError(CRuntimeError::TypeMismatch);
            }

            let mut caller_state = caller_state.clone();
            caller_state.memory = state.memory;
            CFunctionOutcome::Return {
                value,
                state: caller_state,
            }
        }
        CStatementOutcome::Normal(_) => {
            CFunctionOutcome::RuntimeError(CRuntimeError::MissingReturn)
        }
        CStatementOutcome::UndefinedBehavior(undefined_behavior) => {
            CFunctionOutcome::UndefinedBehavior(undefined_behavior)
        }
        CStatementOutcome::RuntimeError(error) => CFunctionOutcome::RuntimeError(error),
    }
}

impl From<u32> for Bitvector32Term {
    fn from(value: u32) -> Self {
        Self::Constant(value)
    }
}

impl From<bool> for ConditionTerm {
    fn from(value: bool) -> Self {
        Self::Constant(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_max_executes_without_list_encoding() {
        let state = c_max_state(int32(0), int32(1));
        let theorem =
            prove_c_statement_execution(state.clone(), c_max_body()).expect("max should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state: state.clone(),
                statement: c_max_body(),
                outcome: CStatementOutcome::Return {
                    value: int32(1),
                    state,
                },
            }
        );
    }

    #[test]
    fn concrete_max_function_call_preserves_caller_locals() {
        let state = CState::new().with_local("caller", int32(99));
        let function = c_max_function();
        let arguments = vec![c_int32_literal(0), c_int32_literal(1)];
        let theorem = prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            arguments.clone(),
            Assumptions::new(),
        )
        .expect("max function call should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CFunctionExecutes {
                state: state.clone(),
                function,
                arguments,
                outcome: CFunctionOutcome::Return {
                    value: int32(1),
                    state,
                },
            }
        );
    }

    #[test]
    fn symbolic_max_function_call_reports_branch_facts() {
        let a = Variable(14);
        let b = Variable(15);
        let a_bits = Bitvector32Term::Variable(a);
        let b_bits = Bitvector32Term::Variable(b);
        let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
        let state = CState::new();
        let function = c_max_function();
        let arguments = vec![
            CExpression::Value(int32(a_bits.clone())),
            CExpression::Value(int32(b_bits.clone())),
        ];
        let execution = prove_symbolic_c_function_execution_paths(
            state.clone(),
            function.clone(),
            arguments.clone(),
            Assumptions::new(),
        );

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].facts(),
            &[PathFact::condition(condition.clone(), true)]
        );
        assert_eq!(
            execution.paths()[0].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[0].theorem().proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition.clone(), true)),
                Box::new(Proposition::CFunctionExecutes {
                    state: state.clone(),
                    function: function.clone(),
                    arguments: arguments.clone(),
                    outcome: CFunctionOutcome::Return {
                        value: int32(b_bits),
                        state: state.clone(),
                    },
                }),
            )
        );

        assert_eq!(
            execution.paths()[1].facts(),
            &[PathFact::condition(condition.clone(), false)]
        );
        assert_eq!(
            execution.paths()[1].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[1].theorem().proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, false)),
                Box::new(Proposition::CFunctionExecutes {
                    state: state.clone(),
                    function,
                    arguments,
                    outcome: CFunctionOutcome::Return {
                        value: int32(a_bits),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn function_call_threads_memory_but_discards_callee_locals() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = CState::new().with_local("caller", int32(42));
        let function = c_function(
            CType::Int32,
            "store_and_load",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_seq(
                c_store(c_variable("p"), c_int32_literal(9)),
                c_return(c_load(c_variable("p"))),
            ),
        );
        let arguments = vec![c_pointer_value(pointer.clone())];
        let final_state = CState::new()
            .with_local("caller", int32(42))
            .with_memory(CMemory::new().store(pointer.clone(), int32(9)));
        let store_obligation = Proposition::CMemoryCanStore {
            memory: CMemory::new(),
            pointer,
        };
        let theorem = prove_symbolic_c_function_execution(
            state.clone(),
            function.clone(),
            arguments.clone(),
            Assumptions::new(),
        )
        .expect("store/load function call should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::Implies(
                Box::new(store_obligation),
                Box::new(Proposition::CFunctionExecutes {
                    state,
                    function,
                    arguments,
                    outcome: CFunctionOutcome::Return {
                        value: int32(9),
                        state: final_state,
                    },
                }),
            )
        );
    }

    #[test]
    fn concrete_function_specification_is_native_theorem() {
        let function = c_max_function();
        let specification = c_function_specification(
            CState::new(),
            vec![c_int32_literal(0), c_int32_literal(1)],
            Vec::new(),
            CFunctionOutcome::Return {
                value: int32(1),
                state: CState::new(),
            },
        );
        let theorem = prove_c_function_satisfies_specification(
            function.clone(),
            specification.clone(),
            Assumptions::new(),
        )
        .expect("concrete max specification should prove");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CFunctionSatisfiesSpecification {
                function,
                specification
            }
        );
    }

    #[test]
    fn symbolic_function_specification_uses_requirements_as_path_facts() {
        let a = Variable(16);
        let b = Variable(17);
        let a_bits = Bitvector32Term::Variable(a);
        let b_bits = Bitvector32Term::Variable(b);
        let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
        let function = c_max_function();
        let specification = c_function_specification(
            CState::new(),
            vec![
                CExpression::Value(int32(a_bits)),
                CExpression::Value(int32(b_bits)),
            ],
            vec![Proposition::ConditionIs(condition.clone(), true)],
            CFunctionOutcome::Return {
                value: int32(Bitvector32Term::Variable(b)),
                state: CState::new(),
            },
        );
        let theorem = prove_c_function_satisfies_specification(
            function.clone(),
            specification.clone(),
            Assumptions::new(),
        )
        .expect("symbolic branch specification should prove under condition");

        assert_eq!(
            theorem.proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, true)),
                Box::new(Proposition::CFunctionSatisfiesSpecification {
                    function,
                    specification
                }),
            )
        );
    }

    #[test]
    fn symbolic_max_branch_specifications_include_bounds() {
        let a = Variable(60);
        let b = Variable(61);
        let a_bits = Bitvector32Term::Variable(a);
        let b_bits = Bitvector32Term::Variable(b);
        let function = c_max_function();
        let arguments = vec![
            CExpression::Value(int32(a_bits.clone())),
            CExpression::Value(int32(b_bits.clone())),
        ];
        let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());

        let right_specification = c_function_specification(
            CState::new(),
            arguments.clone(),
            vec![Proposition::ConditionIs(condition.clone(), true)],
            CFunctionOutcome::Return {
                value: int32(b_bits.clone()),
                state: CState::new(),
            },
        );
        prove_c_function_satisfies_specification_and_propositions(
            function.clone(),
            right_specification,
            Assumptions::new(),
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(b_bits.clone(), a_bits.clone()),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(b_bits.clone(), b_bits.clone()),
                    true,
                ),
            ],
        )
        .expect("under a < b, max returns b and b is >= both inputs");

        let left_specification = c_function_specification(
            CState::new(),
            arguments,
            vec![Proposition::ConditionIs(condition, false)],
            CFunctionOutcome::Return {
                value: int32(a_bits.clone()),
                state: CState::new(),
            },
        );
        prove_c_function_satisfies_specification_and_propositions(
            function,
            left_specification,
            Assumptions::new(),
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(a_bits.clone(), a_bits.clone()),
                    true,
                ),
                Proposition::ConditionIs(ConditionTerm::signed_greater_equal(a_bits, b_bits), true),
            ],
        )
        .expect("under not (a < b), max returns a and a is >= both inputs");
    }

    #[test]
    fn symbolic_clamp_branch_specifications_include_bounds_under_ordered_limits() {
        let x = Variable(62);
        let lo = Variable(63);
        let hi = Variable(64);
        let x_bits = Bitvector32Term::Variable(x);
        let lo_bits = Bitvector32Term::Variable(lo);
        let hi_bits = Bitvector32Term::Variable(hi);
        let ordered_limits = Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(lo_bits.clone(), hi_bits.clone()),
            true,
        );
        let below_lo = ConditionTerm::signed_less_than(x_bits.clone(), lo_bits.clone());
        let above_hi = ConditionTerm::signed_greater_than(x_bits.clone(), hi_bits.clone());
        let function = c_function(
            CType::Int32,
            "clamp",
            vec![
                c_parameter("x", CType::Int32),
                c_parameter("lo", CType::Int32),
                c_parameter("hi", CType::Int32),
            ],
            c_if(
                c_less_than(c_variable("x"), c_variable("lo")),
                c_return(c_variable("lo")),
                c_if(
                    c_greater_than(c_variable("x"), c_variable("hi")),
                    c_return(c_variable("hi")),
                    c_return(c_variable("x")),
                ),
            ),
        );
        let arguments = vec![
            CExpression::Value(int32(x_bits.clone())),
            CExpression::Value(int32(lo_bits.clone())),
            CExpression::Value(int32(hi_bits.clone())),
        ];

        for (requires, result, message) in [
            (
                vec![
                    ordered_limits.clone(),
                    Proposition::ConditionIs(below_lo.clone(), true),
                ],
                lo_bits.clone(),
                "x below lo returns lo within bounds",
            ),
            (
                vec![
                    ordered_limits.clone(),
                    Proposition::ConditionIs(below_lo.clone(), false),
                    Proposition::ConditionIs(above_hi.clone(), true),
                ],
                hi_bits.clone(),
                "x above hi returns hi within bounds",
            ),
            (
                vec![
                    ordered_limits.clone(),
                    Proposition::ConditionIs(below_lo.clone(), false),
                    Proposition::ConditionIs(above_hi.clone(), false),
                ],
                x_bits.clone(),
                "x already in range returns x within bounds",
            ),
        ] {
            let specification = c_function_specification(
                CState::new(),
                arguments.clone(),
                requires,
                CFunctionOutcome::Return {
                    value: int32(result.clone()),
                    state: CState::new(),
                },
            );
            prove_c_function_satisfies_specification_and_propositions(
                function.clone(),
                specification,
                Assumptions::new(),
                vec![
                    Proposition::ConditionIs(
                        ConditionTerm::signed_greater_equal(result.clone(), lo_bits.clone()),
                        true,
                    ),
                    Proposition::ConditionIs(
                        ConditionTerm::signed_less_equal(result, hi_bits.clone()),
                        true,
                    ),
                ],
            )
            .expect(message);
        }
    }

    #[test]
    fn incomplete_symbolic_function_specification_does_not_prove() {
        let a = Variable(18);
        let b = Variable(19);
        let function = c_max_function();
        let specification = c_function_specification(
            CState::new(),
            vec![
                CExpression::Value(int32(Bitvector32Term::Variable(a))),
                CExpression::Value(int32(Bitvector32Term::Variable(b))),
            ],
            Vec::new(),
            CFunctionOutcome::Return {
                value: int32(Bitvector32Term::Variable(b)),
                state: CState::new(),
            },
        );

        assert!(
            prove_c_function_satisfies_specification(function, specification, Assumptions::new())
                .is_none()
        );
    }

    #[test]
    fn call_assign_uses_function_environment() {
        let increment = c_function(
            CType::Int32,
            "increment",
            vec![c_parameter("x", CType::Int32)],
            c_return(c_add(c_variable("x"), c_int32_literal(1))),
        );
        let environment = CFunctionEnvironment::new().with_function(increment);
        let state = CState::new();
        let statement = c_seq(
            c_call_assign("result", "increment", vec![c_int32_literal(41)]),
            c_return(c_variable("result")),
        );
        let final_state = CState::new().with_local("result", int32(42));
        let theorem = prove_symbolic_c_execution_with_environment(
            state.clone(),
            statement.clone(),
            Assumptions::new(),
            environment,
        )
        .expect("known function call should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state,
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(42),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn unknown_call_assign_is_runtime_error() {
        let state = CState::new();
        let statement = c_call_assign("result", "missing", Vec::new());
        let theorem = prove_symbolic_c_execution_with_environment(
            state.clone(),
            statement.clone(),
            Assumptions::new(),
            CFunctionEnvironment::new(),
        )
        .expect("unknown function should produce a single runtime-error path");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state,
                statement,
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                    "missing".to_string(),
                )),
            }
        );
    }

    #[test]
    fn while_loop_executes_concrete_countdown() {
        let state = CState::new().with_local("x", int32(3));
        let loop_statement = c_while(
            c_greater_than(c_variable("x"), c_int32_literal(0)),
            Vec::new(),
            c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
        );
        let statement = c_seq(loop_statement, c_return(c_variable("x")));
        let final_state = CState::new().with_local("x", int32(0));
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("concrete countdown loop should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state,
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(0),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn loop_budget_exhaustion_is_executor_failure_not_c_runtime_error() {
        let state = CState::new().with_local("x", int32(0));
        let statement = c_while(
            c_int32_literal(1),
            Vec::new(),
            c_assign("x", c_variable("x")),
        );
        let budget = ExecutionBudget::new().with_loop_unrolls(2);
        let execution = prove_symbolic_c_execution_paths_with_budget(
            state.clone(),
            statement.clone(),
            Assumptions::new(),
            budget.clone(),
        );

        assert_eq!(execution.limit(), Some(ExecutionLimit::LoopUnrolls));
        assert_eq!(execution.paths(), &[] as &[SymbolicCExecutionPath]);
        assert!(
            prove_symbolic_c_execution_with_budget(state, statement, Assumptions::new(), budget,)
                .is_none()
        );
    }

    #[test]
    fn executor_budgets_cap_steps_calls_and_paths() {
        let state = CState::new();
        let statement = c_return(c_int32_literal(1));

        assert_eq!(
            prove_symbolic_c_execution_paths_with_budget(
                state.clone(),
                statement.clone(),
                Assumptions::new(),
                ExecutionBudget::new().with_statement_steps(0),
            )
            .limit(),
            Some(ExecutionLimit::StatementSteps)
        );
        assert_eq!(
            prove_symbolic_c_execution_paths_with_budget(
                state.clone(),
                statement,
                Assumptions::new(),
                ExecutionBudget::new().with_expression_steps(0),
            )
            .limit(),
            Some(ExecutionLimit::ExpressionSteps)
        );

        let function = c_function(
            CType::Int32,
            "id",
            vec![c_parameter("x", CType::Int32)],
            c_return(c_variable("x")),
        );
        assert_eq!(
            prove_symbolic_c_function_execution_paths_with_budget(
                CState::new(),
                function,
                vec![c_int32_literal(1)],
                Assumptions::new(),
                ExecutionBudget::new().with_function_calls(0),
            )
            .limit(),
            Some(ExecutionLimit::FunctionCalls)
        );

        let a = Variable(75);
        let b = Variable(76);
        let branchy_statement = c_return(c_less_than(
            CExpression::Value(int32(Bitvector32Term::Variable(a))),
            CExpression::Value(int32(Bitvector32Term::Variable(b))),
        ));
        assert_eq!(
            prove_symbolic_c_execution_paths_with_budget(
                state,
                branchy_statement,
                Assumptions::new(),
                ExecutionBudget::new().with_paths(3),
            )
            .limit(),
            Some(ExecutionLimit::Paths)
        );
    }

    #[test]
    fn while_invariant_is_proof_obligation() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let invariant = Proposition::CMemoryCanLoad {
            memory: CMemory::new(),
            pointer,
        };
        let state = CState::new().with_local("x", int32(0));
        let statement = c_while(
            c_greater_than(c_variable("x"), c_int32_literal(0)),
            vec![invariant.clone()],
            c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
        );
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("false loop should execute under invariant obligation");

        assert_eq!(
            theorem.proposition(),
            &Proposition::Implies(
                Box::new(invariant),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement,
                    outcome: CStatementOutcome::Normal(state),
                }),
            )
        );
    }

    #[test]
    fn builtin_obligation_solver_proves_trivial_props() {
        let assumptions = Assumptions::new();
        let memory = CMemory::new().with_block("block", 8);
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };

        assert!(assumptions.proves(&Proposition::Equal(
            Term::Bitvector32(Bitvector32Term::Constant(7)),
            Term::Bitvector32(Bitvector32Term::Constant(7)),
        )));
        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Constant(true),
            true
        )));
        assert!(assumptions.proves(&Proposition::CMemoryCanLoad {
            memory: memory.clone(),
            pointer: pointer.clone(),
        }));
        assert!(assumptions.proves(&Proposition::CMemoryCanStore { memory, pointer }));
    }

    #[test]
    fn assumptions_split_small_finite_context_variable() {
        let j = Bitvector32Term::Variable(Variable(87));
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
                true,
            );
        let proposition = Proposition::Or(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(j, Bitvector32Term::Constant(1)),
                true,
            )),
        );

        assert!(assumptions.proves(&proposition));
    }

    #[test]
    fn finite_forall_order_fact_participates_in_transitive_order_path() {
        let memory = CMemory::new();
        let indexed_load = |index| {
            Bitvector32Term::MemoryLoad(
                Box::new(memory.clone()),
                Box::new(Pointer {
                    block: "arg-memory".to_string(),
                    offset: PointerOffsetTerm::scale_int32(index, 4),
                }),
            )
        };
        let k = Variable(88);
        let k_bits = Bitvector32Term::Variable(k);
        let load_k = indexed_load(k_bits.clone());
        let load_0 = indexed_load(Bitvector32Term::Constant(0));
        let load_1 = indexed_load(Bitvector32Term::Constant(1));
        let load_2 = indexed_load(Bitvector32Term::Constant(2));
        let finite_order_fact = Proposition::ForAll {
            var: k,
            sort: Sort::CInt32,
            body: Box::new(Proposition::Implies(
                Box::new(Proposition::And(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::signed_less_equal(
                            Bitvector32Term::Constant(0),
                            k_bits.clone(),
                        ),
                        true,
                    )),
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::signed_less_than(k_bits, Bitvector32Term::Constant(1)),
                        true,
                    )),
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(load_k, load_1.clone()),
                    true,
                )),
            )),
        };
        let assumptions = Assumptions::new()
            .assume_proposition(finite_order_fact)
            .assume_condition(
                ConditionTerm::signed_less_equal(load_1, load_2.clone()),
                true,
            );

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(load_0, load_2),
            true,
        )));
    }

    #[test]
    fn assumptions_prove_by_bounded_disjunction_cases() {
        let x = Bitvector32Term::Variable(Variable(89));
        let x_is_zero = Proposition::ConditionIs(
            ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(0)),
            true,
        );
        let x_is_one = Proposition::ConditionIs(
            ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(1)),
            true,
        );
        let assumptions = Assumptions::new().assume_proposition(Proposition::Or(
            Box::new(x_is_zero.clone()),
            Box::new(x_is_one.clone()),
        ));

        assert!(assumptions.proves(&Proposition::Or(Box::new(x_is_one), Box::new(x_is_zero),)));
    }

    #[test]
    fn known_memory_block_bounds_prove_symbolic_element_access() {
        let index = Variable(91);
        let index_bits = Bitvector32Term::Variable(index);
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(
                    index_bits.clone(),
                    Bitvector32Term::Constant(0),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(index_bits.clone(), Bitvector32Term::Constant(3)),
                true,
            );
        let memory = CMemory::new().with_block("local:a", 12);
        let pointer = CMemory::local_pointer("a").offset_by_int32_elements(index_bits);

        assert!(assumptions.proves(&Proposition::CMemoryCanLoad {
            memory: memory.clone(),
            pointer: pointer.clone(),
        }));
        assert!(assumptions.proves(&Proposition::CMemoryCanStore { memory, pointer }));
    }

    #[test]
    fn assumptions_prove_forall_int32_array_range_body() {
        let index = Variable(90);
        let index_bits = Bitvector32Term::Variable(index);
        let memory = CMemory::new().with_block("block", 12);
        let base = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let indexed_pointer = base.offset_by_int32_elements(index_bits.clone());
        let in_segment = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    index_bits.clone(),
                    Bitvector32Term::Constant(0),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(index_bits, Bitvector32Term::Constant(3)),
                true,
            )),
        );
        let can_load_index = Proposition::CMemoryCanLoad {
            memory: memory.clone(),
            pointer: indexed_pointer,
        };
        let assumptions = Assumptions::new().assume_proposition(Proposition::CMemoryValidRange {
            memory,
            base,
            bytes: Bitvector32Term::Constant(12),
        });

        assert!(assumptions.proves(&forall_int32(
            index,
            Proposition::Implies(Box::new(in_segment), Box::new(can_load_index)),
        )));
    }

    #[test]
    fn assumptions_prove_finite_forall_int32_by_instantiation() {
        let i = Variable(92);
        let j = Variable(93);
        let i_bits = Bitvector32Term::Variable(i);
        let j_bits = Bitvector32Term::Variable(j);
        let antecedent = Proposition::And(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(
                        i_bits.clone(),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(
                        j_bits.clone(),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(i_bits.clone(), j_bits.clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(j_bits, Bitvector32Term::Constant(3)),
                    true,
                )),
            )),
        );
        let consequent = Proposition::Or(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(i_bits, Bitvector32Term::Constant(1)),
                true,
            )),
        );

        assert!(Assumptions::new().proves(&forall_int32(
            i,
            forall_int32(
                j,
                Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
            ),
        )));
    }

    #[test]
    fn order_solver_uses_negated_less_than_transitively() {
        let a = Bitvector32Term::Variable(Variable(94));
        let b = Bitvector32Term::Variable(Variable(95));
        let c = Bitvector32Term::Variable(Variable(96));
        let assumptions = Assumptions::new()
            .assume_condition(ConditionTerm::signed_less_than(b.clone(), a.clone()), false)
            .assume_condition(ConditionTerm::signed_less_than(c.clone(), b), false);

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(a, c),
            true,
        )));
    }

    #[test]
    fn assumptions_do_not_prove_implication_by_treating_unknown_antecedent_as_false() {
        let x = Bitvector32Term::Variable(Variable(91));
        let antecedent = Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
            true,
        );
        let consequent =
            Proposition::ConditionIs(ConditionTerm::equal(x, Bitvector32Term::Constant(0)), true);

        assert!(!Assumptions::new().proves(&Proposition::Implies(
            Box::new(antecedent),
            Box::new(consequent),
        )));
    }

    #[test]
    fn builtin_obligation_solver_discharges_concrete_invariant() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().with_block("block", 4);
        let invariant = Proposition::CMemoryCanLoad {
            memory: memory.clone(),
            pointer,
        };
        let state = CState::new().with_local("x", int32(0)).with_memory(memory);
        let statement = c_while(
            c_greater_than(c_variable("x"), c_int32_literal(0)),
            vec![invariant],
            c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
        );
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("concrete invariant should be solved");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Normal(state),
            }
        );
    }

    #[test]
    fn countdown_loop_body_preserves_nonnegative_invariant_symbolically() {
        let x = Variable(66);
        let x_bits = Bitvector32Term::Variable(x);
        let state = CState::new().with_local("x", int32(x_bits.clone()));
        let statement = c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1)));
        let invariant =
            ConditionTerm::signed_greater_equal(x_bits.clone(), Bitvector32Term::Constant(0));
        let condition =
            ConditionTerm::signed_greater_than(x_bits.clone(), Bitvector32Term::Constant(0));
        let post_invariant = Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(
                Bitvector32Term::Subtract(
                    Box::new(x_bits.clone()),
                    Box::new(Bitvector32Term::Constant(1)),
                ),
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        let assumptions = Assumptions::new()
            .assume_condition(invariant.clone(), true)
            .assume_condition(condition.clone(), true);
        let theorem = prove_c_statement_executes_and_propositions(
            state.clone(),
            statement.clone(),
            assumptions,
            vec![post_invariant.clone()],
        )
        .expect("x > 0 should prove x - 1 executes and remains nonnegative");

        assert_eq!(
            theorem.proposition().peel_implications(),
            &proposition_and(
                Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement,
                    outcome: CStatementOutcome::Normal(CState::new().with_local(
                        "x",
                        int32(Bitvector32Term::Subtract(
                            Box::new(x_bits),
                            Box::new(Bitvector32Term::Constant(1)),
                        )),
                    ),),
                },
                post_invariant,
            )
        );
    }

    #[test]
    fn symbolic_max_lt_branch_is_native_theorem() {
        let a = Variable(10);
        let b = Variable(11);
        let theorem = prove_c_max_lt_returns_right(a, b).expect("lt branch should prove");
        let condition = ConditionTerm::Bitvector32SignedLessThan(
            Box::new(Bitvector32Term::Variable(a)),
            Box::new(Bitvector32Term::Variable(b)),
        );
        let state = c_max_state(
            int32(Bitvector32Term::Variable(a)),
            int32(Bitvector32Term::Variable(b)),
        );

        assert_eq!(
            theorem.proposition(),
            &forall_int32(
                a,
                forall_int32(
                    b,
                    Proposition::Implies(
                        Box::new(Proposition::ConditionIs(condition, true)),
                        Box::new(Proposition::CStatementExecutes {
                            state: state.clone(),
                            statement: c_max_body(),
                            outcome: CStatementOutcome::Return {
                                value: int32(Bitvector32Term::Variable(b)),
                                state,
                            },
                        }),
                    ),
                ),
            )
        );
    }

    #[test]
    fn symbolic_max_not_lt_branch_is_native_theorem() {
        let a = Variable(12);
        let b = Variable(13);
        let theorem = prove_c_max_not_lt_returns_left(a, b).expect("false branch should prove");
        let condition = ConditionTerm::Bitvector32SignedLessThan(
            Box::new(Bitvector32Term::Variable(a)),
            Box::new(Bitvector32Term::Variable(b)),
        );
        let state = c_max_state(
            int32(Bitvector32Term::Variable(a)),
            int32(Bitvector32Term::Variable(b)),
        );

        assert_eq!(
            theorem.proposition(),
            &forall_int32(
                a,
                forall_int32(
                    b,
                    Proposition::Implies(
                        Box::new(Proposition::ConditionIs(condition, false)),
                        Box::new(Proposition::CStatementExecutes {
                            state: state.clone(),
                            statement: c_max_body(),
                            outcome: CStatementOutcome::Return {
                                value: int32(Bitvector32Term::Variable(a)),
                                state,
                            },
                        }),
                    ),
                ),
            )
        );
    }

    #[test]
    fn signed_add_overflow_is_native_undefined_behavior() {
        let state = CState::new();
        let theorem = prove_c_expression_evaluation(
            state.clone(),
            c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
        )
        .expect("concrete add should evaluate");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state,
                expression: c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            }
        );
    }

    #[test]
    fn int32_subtraction_is_native() {
        let state = CState::new();
        let statement = c_return(c_subtract(c_int32_literal(7), c_int32_literal(2)));
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("concrete subtraction should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(5),
                    state,
                },
            }
        );
    }

    #[test]
    fn signed_subtract_overflow_is_native_undefined_behavior() {
        let state = CState::new();
        let theorem = prove_c_expression_evaluation(
            state.clone(),
            c_subtract(c_int32_literal(2_147_483_648), c_int32_literal(1)),
        )
        .expect("concrete subtraction should evaluate");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state,
                expression: c_subtract(c_int32_literal(2_147_483_648), c_int32_literal(1)),
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            }
        );
    }

    #[test]
    fn int32_comparisons_return_c_int32_zero_or_one() {
        let state = CState::new();
        let examples = [
            (
                c_less_equal(c_int32_literal(2), c_int32_literal(2)),
                int32(1),
            ),
            (
                c_greater_than(c_int32_literal(3), c_int32_literal(2)),
                int32(1),
            ),
            (
                c_greater_equal(c_int32_literal(2), c_int32_literal(3)),
                int32(0),
            ),
            (c_equal(c_int32_literal(4), c_int32_literal(4)), int32(1)),
        ];

        for (expression, expected) in examples {
            let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
                .expect("comparison should evaluate");
            assert_eq!(
                theorem.proposition(),
                &Proposition::CExpressionEvaluates {
                    state: state.clone(),
                    expression,
                    outcome: CExpressionOutcome::Value(expected),
                }
            );
        }
    }

    #[test]
    fn pointer_equality_returns_c_int32_zero_or_one() {
        let p = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let same = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let next = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let other = Pointer {
            block: "other".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = CState::new()
            .with_local("p", CValue::Pointer(p))
            .with_local("same", CValue::Pointer(same))
            .with_local("next", CValue::Pointer(next))
            .with_local("other", CValue::Pointer(other));
        let examples = [
            (c_equal(c_variable("p"), c_variable("same")), int32(1)),
            (c_equal(c_variable("p"), c_variable("next")), int32(0)),
            (c_equal(c_variable("p"), c_variable("other")), int32(0)),
        ];

        for (expression, expected) in examples {
            let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
                .expect("pointer equality should evaluate");
            assert_eq!(
                theorem.proposition(),
                &Proposition::CExpressionEvaluates {
                    state: state.clone(),
                    expression,
                    outcome: CExpressionOutcome::Value(expected),
                }
            );
        }
    }

    #[test]
    fn pointer_equality_accepts_int32_zero_as_null_pointer_constant() {
        let null = Pointer {
            block: "null".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let nonnull = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = CState::new()
            .with_local("nullp", CValue::Pointer(null))
            .with_local("p", CValue::Pointer(nonnull));
        let examples = [
            (c_equal(c_variable("nullp"), c_int32_literal(0)), int32(1)),
            (c_equal(c_int32_literal(0), c_variable("nullp")), int32(1)),
            (c_equal(c_variable("p"), c_int32_literal(0)), int32(0)),
        ];

        for (expression, expected) in examples {
            let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
                .expect("null equality should evaluate");
            assert_eq!(
                theorem.proposition(),
                &Proposition::CExpressionEvaluates {
                    state: state.clone(),
                    expression,
                    outcome: CExpressionOutcome::Value(expected),
                }
            );
        }

        let invalid = c_equal(c_variable("p"), c_int32_literal(1));
        let theorem = prove_c_expression_evaluation(state.clone(), invalid.clone())
            .expect("invalid pointer equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state,
                expression: invalid,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            }
        );
    }

    #[test]
    fn not_equal_and_not_return_c_int32_zero_or_one() {
        let null = Pointer {
            block: "null".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let p = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let same = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let next = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let state = CState::new()
            .with_local("nullp", CValue::Pointer(null))
            .with_local("p", CValue::Pointer(p))
            .with_local("same", CValue::Pointer(same))
            .with_local("next", CValue::Pointer(next));
        let examples = [
            (
                c_not_equal(c_int32_literal(4), c_int32_literal(5)),
                int32(1),
            ),
            (c_not_equal(c_variable("p"), c_variable("same")), int32(0)),
            (c_not_equal(c_variable("p"), c_variable("next")), int32(1)),
            (
                c_not_equal(c_variable("nullp"), c_int32_literal(0)),
                int32(0),
            ),
            (c_not(c_int32_literal(0)), int32(1)),
            (c_not(c_int32_literal(7)), int32(0)),
            (c_not(c_variable("nullp")), int32(1)),
            (c_not(c_variable("p")), int32(0)),
        ];

        for (expression, expected) in examples {
            let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
                .expect("logical expression should evaluate");
            assert_eq!(
                theorem.proposition(),
                &Proposition::CExpressionEvaluates {
                    state: state.clone(),
                    expression,
                    outcome: CExpressionOutcome::Value(expected),
                }
            );
        }
    }

    #[test]
    fn logical_and_or_short_circuit_right_operand() {
        let invalid_pointer = Pointer {
            block: "missing".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let invalid_load = c_load(c_pointer_value(invalid_pointer));
        let state = CState::new();
        let examples = [
            (c_and(c_int32_literal(0), invalid_load.clone()), int32(0)),
            (c_or(c_int32_literal(1), invalid_load.clone()), int32(1)),
        ];

        for (expression, expected) in examples {
            let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
                .expect("short-circuit expression should evaluate");
            assert_eq!(
                theorem.proposition(),
                &Proposition::CExpressionEvaluates {
                    state: state.clone(),
                    expression,
                    outcome: CExpressionOutcome::Value(expected),
                }
            );
        }

        assert!(
            prove_c_expression_evaluation(
                state.clone(),
                c_and(c_int32_literal(1), invalid_load.clone()),
            )
            .is_none()
        );
        assert!(
            prove_c_expression_evaluation(state, c_or(c_int32_literal(0), invalid_load)).is_none()
        );
    }

    #[test]
    fn symbolic_pointer_equality_reports_branch_facts() {
        let offset = Variable(80);
        let left = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let right = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Variable(offset),
        };
        let condition =
            ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone());
        let state = CState::new()
            .with_local("p", CValue::Pointer(left))
            .with_local("q", CValue::Pointer(right));
        let statement = c_if(
            c_equal(c_variable("p"), c_variable("q")),
            c_return(c_int32_literal(1)),
            c_return(c_int32_literal(0)),
        );
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].facts(),
            &[PathFact::condition(condition.clone(), true)]
        );
        assert_eq!(
            execution.paths()[0]
                .theorem()
                .proposition()
                .peel_implications(),
            &Proposition::CStatementExecutes {
                state: state.clone(),
                statement: statement.clone(),
                outcome: CStatementOutcome::Return {
                    value: int32(1),
                    state: state.clone(),
                },
            }
        );
        assert_eq!(
            execution.paths()[1].facts(),
            &[PathFact::condition(condition, false)]
        );
        assert_eq!(
            execution.paths()[1]
                .theorem()
                .proposition()
                .peel_implications(),
            &Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(0),
                    state,
                },
            }
        );
    }

    #[test]
    fn if_uses_c_int32_truthiness() {
        let state = CState::new();
        let statement = c_if(
            c_int32_literal(7),
            c_return(c_int32_literal(1)),
            c_return(c_int32_literal(0)),
        );
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("nonzero int32 condition should take then branch");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(1),
                    state,
                },
            }
        );

        let state = CState::new();
        let statement = c_if(
            c_int32_literal(0),
            c_return(c_int32_literal(1)),
            c_return(c_int32_literal(0)),
        );
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("zero int32 condition should take else branch");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(0),
                    state,
                },
            }
        );
    }

    #[test]
    fn assignment_and_sequence_update_native_state() {
        let state = CState::new().with_local("x", int32(0));
        let statement = c_seq(c_assign("x", c_int32_literal(2)), c_return(c_variable("x")));
        let final_state = CState::new().with_local("x", int32(2));
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("assignment sequence should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state,
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(2),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn store_then_load_threads_native_memory() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = CState::new();
        let statement = c_seq(
            c_store(c_pointer_value(pointer.clone()), c_int32_literal(9)),
            c_return(c_load(c_pointer_value(pointer.clone()))),
        );
        let final_state =
            CState::new().with_memory(CMemory::new().store(pointer.clone(), int32(9)));
        let store_obligation = Proposition::CMemoryCanStore {
            memory: CMemory::new(),
            pointer,
        };
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("store then load should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::Implies(
                Box::new(store_obligation),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement,
                    outcome: CStatementOutcome::Return {
                        value: int32(9),
                        state: final_state,
                    },
                }),
            )
        );
    }

    #[test]
    fn symbolic_load_from_incomplete_memory_reports_validity_obligation() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let state = CState::new().with_local("p", CValue::Pointer(pointer.clone()));
        let statement = c_return(c_load(c_variable("p")));
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

        assert_eq!(execution.paths().len(), 1);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[ProofObligation::memory_can_load(
                CMemory::new(),
                pointer.clone()
            )]
        );
        assert_eq!(
            execution.paths()[0].theorem().proposition(),
            &Proposition::Implies(
                Box::new(Proposition::CMemoryCanLoad {
                    memory: CMemory::new(),
                    pointer: pointer.clone(),
                }),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement,
                    outcome: CStatementOutcome::Return {
                        value: int32(Bitvector32Term::MemoryLoad(
                            Box::new(CMemory::new()),
                            Box::new(pointer),
                        )),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn block_backed_store_then_load_needs_no_memory_obligation() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().with_block("block", 16);
        let state = CState::new().with_memory(memory.clone());
        let statement = c_seq(
            c_store(c_pointer_value(pointer.clone()), c_int32_literal(9)),
            c_return(c_load(c_pointer_value(pointer.clone()))),
        );
        let final_state = CState::new().with_memory(memory.store(pointer, int32(9)));
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("in-range block store/load should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state,
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(9),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn block_backed_missing_load_returns_symbolic_value_without_obligation() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let memory = CMemory::new().with_block("block", 16);
        let state = CState::new()
            .with_local("p", CValue::Pointer(pointer.clone()))
            .with_memory(memory.clone());
        let statement = c_return(c_load(c_variable("p")));
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("in-range missing load should produce symbolic value");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::MemoryLoad(
                        Box::new(memory),
                        Box::new(pointer)
                    )),
                    state,
                },
            }
        );
    }

    #[test]
    fn pointer_addition_scales_int32_offsets_for_loads() {
        let base = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let second = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let memory = CMemory::new()
            .with_block("block", 16)
            .store(second, int32(23));
        let state = CState::new()
            .with_local("p", CValue::Pointer(base))
            .with_memory(memory);
        let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("pointer arithmetic load should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state,
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(23),
                    state: CState::new()
                        .with_local(
                            "p",
                            CValue::Pointer(Pointer {
                                block: "block".to_string(),
                                offset: PointerOffsetTerm::Constant(0),
                            }),
                        )
                        .with_memory(CMemory::new().with_block("block", 16).store(
                            Pointer {
                                block: "block".to_string(),
                                offset: PointerOffsetTerm::Constant(4),
                            },
                            int32(23),
                        ),),
                },
            }
        );
    }

    #[test]
    fn pointer_addition_out_of_range_load_reports_validity_obligation() {
        let base = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let derived = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let memory = CMemory::new().with_block("block", 4);
        let state = CState::new()
            .with_local("p", CValue::Pointer(base))
            .with_memory(memory.clone());
        let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

        assert_eq!(execution.paths().len(), 1);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[ProofObligation::memory_can_load(
                memory.clone(),
                derived.clone()
            )]
        );
        assert_eq!(
            execution.paths()[0].theorem().proposition(),
            &Proposition::Implies(
                Box::new(Proposition::CMemoryCanLoad {
                    memory: memory.clone(),
                    pointer: derived.clone(),
                }),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement,
                    outcome: CStatementOutcome::Return {
                        value: int32(Bitvector32Term::MemoryLoad(
                            Box::new(memory),
                            Box::new(derived),
                        )),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn fixed_bound_store_loop_touches_only_valid_pointer_range() {
        let base = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().with_block("block", 12);
        let state = CState::new()
            .with_local("p", CValue::Pointer(base))
            .with_local("i", int32(0))
            .with_memory(memory.clone());
        let loop_statement = c_while(
            c_less_than(c_variable("i"), c_int32_literal(3)),
            Vec::new(),
            c_seq(
                c_store(c_add(c_variable("p"), c_variable("i")), c_variable("i")),
                c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
            ),
        );
        let statement = c_seq(loop_statement, c_return(c_variable("i")));
        let final_memory = memory
            .store(
                Pointer {
                    block: "block".to_string(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                int32(0),
            )
            .store(
                Pointer {
                    block: "block".to_string(),
                    offset: PointerOffsetTerm::Constant(4),
                },
                int32(1),
            )
            .store(
                Pointer {
                    block: "block".to_string(),
                    offset: PointerOffsetTerm::Constant(8),
                },
                int32(2),
            );
        let final_state = CState::new()
            .with_local(
                "p",
                CValue::Pointer(Pointer {
                    block: "block".to_string(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
            )
            .with_local("i", int32(3))
            .with_memory(final_memory);
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

        assert_eq!(execution.paths().len(), 1);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[0].theorem().proposition(),
            &Proposition::CStatementExecutes {
                state,
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(3),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn symbolic_valid_range_discharges_pointer_access_obligation() {
        let i = Variable(67);
        let n = Variable(68);
        let i_bits = Bitvector32Term::Variable(i);
        let n_bits = Bitvector32Term::Variable(n);
        let memory = CMemory::new();
        let base = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = CState::new()
            .with_local("p", CValue::Pointer(base.clone()))
            .with_local("i", int32(i_bits.clone()))
            .with_memory(memory.clone());
        let statement = c_store(c_add(c_variable("p"), c_variable("i")), c_int32_literal(7));
        let assumptions = Assumptions::new()
            .assume_proposition(Proposition::CMemoryValidRange {
                memory: memory.clone(),
                base: base.clone(),
                bytes: Bitvector32Term::Multiply(
                    Box::new(n_bits.clone()),
                    Box::new(Bitvector32Term::Constant(4)),
                ),
            })
            .assume_condition(
                ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(i_bits.clone(), n_bits),
                true,
            );
        let execution = prove_symbolic_c_execution_paths(state, statement, assumptions);

        assert_eq!(execution.paths().len(), 1);
        assert_eq!(
            execution.paths()[0].obligations(),
            &[] as &[ProofObligation]
        );
    }

    #[test]
    fn interval_arithmetic_proves_increment_bounds_and_no_overflow() {
        let i = Variable(69);
        let n = Variable(70);
        let i_bits = Bitvector32Term::Variable(i);
        let n_bits = Bitvector32Term::Variable(n);
        let incremented = Bitvector32Term::Add(
            Box::new(i_bits.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        );
        let state = CState::new().with_local("i", int32(i_bits.clone()));
        let statement = c_assign("i", c_add(c_variable("i"), c_int32_literal(1)));
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(i_bits.clone(), n_bits.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    n_bits.clone(),
                    Bitvector32Term::Constant(i32::MAX as u32),
                ),
                true,
            );
        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_less_than(i_bits.clone(), incremented.clone()),
            true,
        )));
        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(i_bits.clone(), incremented.clone()),
            true,
        )));
        let theorem = prove_c_statement_executes_and_propositions(
            state,
            statement,
            assumptions,
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(
                        incremented.clone(),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(incremented, n_bits),
                    true,
                ),
            ],
        )
        .expect("interval facts should prove i + 1 bounds and no signed overflow");

        assert!(matches!(theorem.proposition(), Proposition::Implies(_, _)));
    }

    #[test]
    fn interval_arithmetic_uses_lower_bound_for_incremented_values() {
        let i = Variable(73);
        let i_bits = Bitvector32Term::Variable(i);
        let incremented = Bitvector32Term::Add(
            Box::new(i_bits.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        );
        let assumptions = Assumptions::new().assume_condition(
            ConditionTerm::signed_greater_equal(i_bits, Bitvector32Term::Constant(1)),
            true,
        );

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(1),),
            true,
        )));
        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(incremented, Bitvector32Term::Constant(0)),
            true,
        )));
    }

    #[test]
    fn negative_equality_fact_decides_equality_false() {
        let x = Bitvector32Term::Variable(Variable(79));
        let assumptions = Assumptions::new().assume_condition(
            ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(0)),
            false,
        );

        assert_eq!(
            assumptions.decide(&ConditionTerm::equal(Bitvector32Term::Constant(0), x,)),
            Some(false)
        );
    }

    #[test]
    fn equality_facts_are_transitive() {
        let i = Bitvector32Term::Variable(Variable(84));
        let k = Bitvector32Term::Variable(Variable(85));
        let assumptions = Assumptions::new()
            .assume_condition(ConditionTerm::equal(k.clone(), i.clone()), true)
            .assume_condition(ConditionTerm::equal(i, Bitvector32Term::Constant(1)), true);

        assert_eq!(
            assumptions.decide(&ConditionTerm::equal(k, Bitvector32Term::Constant(1))),
            Some(true)
        );
    }

    #[test]
    fn excluded_small_integer_range_is_inconsistent() {
        let k = Bitvector32Term::Variable(Variable(80));
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(3)),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(0)),
                false,
            )
            .assume_condition(
                ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(1)),
                false,
            )
            .assume_condition(ConditionTerm::equal(k, Bitvector32Term::Constant(2)), false);

        assert!(assumptions.proves(&false_equals_true_proposition()));
    }

    #[test]
    fn singleton_integer_range_forces_equality() {
        let k = Bitvector32Term::Variable(Variable(86));
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(1)),
                true,
            );

        assert_eq!(
            assumptions.decide(&ConditionTerm::equal(k, Bitvector32Term::Constant(0))),
            Some(true)
        );
    }

    #[test]
    fn mutable_frame_proves_unwritten_load_equal_across_stack_locals() {
        let i = Variable(74);
        let i_bits = Bitvector32Term::Variable(i);
        let old_memory = CMemory::new();
        let loop_entry_memory = CMemory::new()
            .with_block("local:i", 4)
            .store(CMemory::local_pointer("i"), int32(1));
        let loop_exit_memory = CMemory::new()
            .with_block("local:i", 4)
            .store(CMemory::local_pointer("i"), int32(i_bits.clone()));
        let first_cell = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let written_cell = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(i_bits.clone()),
                byte_width: 4,
            },
        };
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(i_bits, Bitvector32Term::Constant(1)),
                true,
            )
            .assume_proposition(Proposition::CMemoryMutatesOnly {
                before: loop_entry_memory,
                after: loop_exit_memory.clone(),
                pointers: vec![written_cell],
            });

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    Box::new(loop_exit_memory),
                    Box::new(first_cell.clone()),
                ),
                Bitvector32Term::MemoryLoad(Box::new(old_memory), Box::new(first_cell)),
            ),
            true,
        )));
    }

    #[test]
    fn unrelated_external_cell_store_preserves_memory_load_with_stack_temporary() {
        let old_memory = CMemory::new();
        let p0 = Pointer {
            block: "arg-memory".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let p1 = Pointer {
            block: "arg-memory".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let stack_memory = CMemory::new()
            .with_block("local:tmp", 4)
            .store(CMemory::local_pointer("tmp"), int32(0));
        let current_memory = stack_memory.clone().store(
            p0.clone(),
            int32(Bitvector32Term::MemoryLoad(
                Box::new(stack_memory),
                Box::new(p0),
            )),
        );

        assert!(Assumptions::new().proves(&Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(Box::new(current_memory), Box::new(p1.clone())),
                Bitvector32Term::MemoryLoad(Box::new(old_memory), Box::new(p1)),
            ),
            true,
        )));
    }

    #[test]
    fn equivalent_memory_load_order_facts_can_be_inconsistent() {
        let old_memory = CMemory::new();
        let stack_memory = CMemory::new()
            .with_block("local:tmp", 4)
            .store(CMemory::local_pointer("tmp"), int32(0));
        let p0 = Pointer {
            block: "arg-memory".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let old_p0 = Bitvector32Term::MemoryLoad(Box::new(old_memory), Box::new(p0.clone()));
        let stack_p0 = Bitvector32Term::MemoryLoad(Box::new(stack_memory), Box::new(p0));
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_less_than(old_p0.clone(), stack_p0.clone()),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_than(stack_p0, old_p0), true);

        assert!(assumptions.proves(&false_equals_true_proposition()));
    }

    #[test]
    fn equivalent_condition_facts_with_different_truth_values_are_inconsistent() {
        let p0 = Pointer {
            block: "arg-memory".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let p1 = Pointer {
            block: "arg-memory".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let memory_a = CMemory::new()
            .with_block("local:i", 4)
            .store(CMemory::local_pointer("i"), int32(0));
        let memory_b = CMemory::new()
            .with_block("local:i", 4)
            .store(CMemory::local_pointer("i"), int32(1));
        let left_a = Bitvector32Term::MemoryLoad(Box::new(memory_a.clone()), Box::new(p0.clone()));
        let right_a = Bitvector32Term::MemoryLoad(Box::new(memory_a), Box::new(p1.clone()));
        let left_b = Bitvector32Term::MemoryLoad(Box::new(memory_b.clone()), Box::new(p0));
        let right_b = Bitvector32Term::MemoryLoad(Box::new(memory_b), Box::new(p1));
        let assumptions = Assumptions::new()
            .assume_condition(ConditionTerm::signed_less_than(left_a, right_a), true)
            .assume_condition(ConditionTerm::signed_less_than(left_b, right_b), false);

        assert!(assumptions.proves(&false_equals_true_proposition()));
    }

    #[test]
    fn disjoint_range_proves_mutable_frame_cell_distinct() {
        let i = Variable(81);
        let j = Variable(82);
        let i_bits = Bitvector32Term::Variable(i);
        let j_bits = Bitvector32Term::Variable(j);
        let before_memory = CMemory::new();
        let after_memory = CMemory::new();
        let base = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let written_cell = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(i_bits.clone()),
                byte_width: 4,
            },
        };
        let read_cell = Pointer {
            block: "p".to_string(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(j_bits.clone()),
                byte_width: 4,
            },
        };
        let i_plus_one = Bitvector32Term::Add(
            Box::new(i_bits.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        );
        let j_plus_one = Bitvector32Term::Add(
            Box::new(j_bits.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        );
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_less_than(i_bits.clone(), i_plus_one.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(j_bits.clone(), j_plus_one.clone()),
                true,
            )
            .assume_proposition(Proposition::CMemoryDisjoint {
                left_base: base.clone(),
                left_start: i_bits.clone(),
                left_end: i_plus_one,
                right_base: base,
                right_start: j_bits.clone(),
                right_end: j_plus_one,
            })
            .assume_proposition(Proposition::CMemoryMutatesOnly {
                before: before_memory.clone(),
                after: after_memory.clone(),
                pointers: vec![written_cell],
            });

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(Box::new(after_memory), Box::new(read_cell.clone())),
                Bitvector32Term::MemoryLoad(Box::new(before_memory), Box::new(read_cell)),
            ),
            true,
        )));
    }

    #[test]
    fn covering_disjoint_fact_handles_shifted_mutable_range() {
        let n = Variable(83);
        let k = Variable(84);
        let n_bits = Bitvector32Term::Variable(n);
        let k_bits = Bitvector32Term::Variable(k);
        let before_memory = CMemory::new();
        let after_memory = CMemory::new();
        let dst_base = Pointer {
            block: "arg-memory".to_string(),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(85)), 4),
        };
        let src_base = Pointer {
            block: "arg-memory".to_string(),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(86)), 4),
        };
        let src_cell = src_base.offset_by_int32_elements(k_bits.clone());
        let shifted_dst = dst_base.offset_by_int32_elements(Bitvector32Term::Constant(1));
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(k_bits, n_bits.clone()),
                true,
            )
            .assume_proposition(Proposition::CMemoryDisjoint {
                left_base: dst_base,
                left_start: Bitvector32Term::Constant(0),
                left_end: n_bits.clone(),
                right_base: src_base,
                right_start: Bitvector32Term::Constant(0),
                right_end: n_bits.clone(),
            })
            .assume_proposition(Proposition::CMemoryEffectSummary {
                before: before_memory.clone(),
                after: after_memory.clone(),
                mutable_ranges: vec![CMemoryRange::new(
                    shifted_dst,
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::subtract(n_bits, Bitvector32Term::Constant(1)),
                )],
            });

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(Box::new(after_memory), Box::new(src_cell.clone())),
                Bitvector32Term::MemoryLoad(Box::new(before_memory), Box::new(src_cell)),
            ),
            true,
        )));
    }

    #[test]
    fn while_invariant_rule_proves_symbolic_loop_exit_fact() {
        let i = Variable(71);
        let n = Variable(72);
        let i_bits = Bitvector32Term::Variable(i);
        let n_bits = Bitvector32Term::Variable(n);
        let incremented = Bitvector32Term::Add(
            Box::new(i_bits.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        );
        let state = CState::new()
            .with_local("i", int32(i_bits.clone()))
            .with_local("n", int32(n_bits.clone()));
        let condition = c_less_than(c_variable("i"), c_variable("n"));
        let body = c_assign("i", c_add(c_variable("i"), c_int32_literal(1)));
        let invariant = vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(i_bits.clone(), n_bits.clone()),
                true,
            ),
        ];
        let assumptions = invariant
            .iter()
            .cloned()
            .fold(Assumptions::new(), Assumptions::assume_proposition)
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    n_bits.clone(),
                    Bitvector32Term::Constant(i32::MAX as u32),
                ),
                true,
            );
        let theorem = prove_c_while_invariant_rule(
            state,
            condition,
            invariant,
            body,
            assumptions,
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(
                        incremented.clone(),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(incremented, n_bits.clone()),
                    true,
                ),
            ],
            Proposition::ConditionIs(ConditionTerm::equal(i_bits, n_bits), true),
        )
        .expect("invariant rule should prove preservation and i == n on loop exit");

        assert!(matches!(theorem.proposition(), Proposition::Implies(_, _)));
    }

    #[test]
    fn same_block_frame_uses_symbolic_offset_inequality() {
        let i = Variable(73);
        let j = Variable(74);
        let i_bits = Bitvector32Term::Variable(i);
        let j_bits = Bitvector32Term::Variable(j);
        let base = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let stored_pointer = base.offset_by_int32_elements(i_bits);
        let loaded_pointer = base.offset_by_int32_elements(j_bits);
        let memory = CMemory::new().store(loaded_pointer.clone(), int32(42));
        let assumptions = Assumptions::new().assume_condition(
            ConditionTerm::pointer_offset_equal(
                stored_pointer.offset.clone(),
                loaded_pointer.offset.clone(),
            ),
            false,
        );
        let theorem = prove_memory_load_after_store_distinct_under_assumptions(
            memory.clone(),
            stored_pointer.clone(),
            int32(9),
            loaded_pointer.clone(),
            assumptions,
        )
        .expect("i != j should prove store p[i] preserves load p[j]");

        assert_eq!(
            theorem.proposition().peel_implications(),
            &Proposition::CMemoryLoads {
                memory: memory.store(stored_pointer, int32(9)),
                pointer: loaded_pointer,
                outcome: CExpressionOutcome::Value(int32(42)),
            }
        );
    }

    #[test]
    fn same_symbolic_base_constant_offsets_are_distinct() {
        let base = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4);
        let first = Pointer {
            block: "arg-memory".to_string(),
            offset: base.clone(),
        };
        let second = Pointer {
            block: "arg-memory".to_string(),
            offset: PointerOffsetTerm::add(base, PointerOffsetTerm::Constant(4)),
        };

        assert!(pointers_proven_distinct(
            &first,
            &second,
            &Assumptions::new()
        ));
    }

    #[test]
    fn additive_equality_cancellation_feeds_range_contradictions() {
        let base = Bitvector32Term::Variable(Variable(91));
        let index = Bitvector32Term::Variable(Variable(92));
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::equal(Bitvector32Term::add(base.clone(), index.clone()), base),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_greater_equal(index, Bitvector32Term::Constant(1)),
                true,
            );

        assert!(assumptions.is_inconsistent());
    }

    #[test]
    fn range_fold_simplifies_empty_and_one_step_ranges() {
        let accumulator = Variable(93);
        let item = Variable(94);
        let x = Bitvector32Term::Variable(Variable(95));
        let body = Bitvector32Term::add(Bitvector32Term::Variable(accumulator), x.clone());

        assert_eq!(
            Bitvector32Term::range_fold(
                Bitvector32Term::Constant(4),
                Bitvector32Term::Constant(4),
                Bitvector32Term::Constant(7),
                accumulator,
                item,
                body.clone(),
            ),
            Bitvector32Term::Constant(7)
        );

        assert_eq!(
            Bitvector32Term::range_fold(
                Bitvector32Term::Variable(Variable(96)),
                Bitvector32Term::add(
                    Bitvector32Term::Variable(Variable(96)),
                    Bitvector32Term::Constant(1)
                ),
                Bitvector32Term::Constant(7),
                accumulator,
                item,
                body,
            ),
            Bitvector32Term::add(Bitvector32Term::Constant(7), x)
        );
    }

    #[test]
    fn count_shaped_range_fold_split_is_proven_equal() {
        let lo = Bitvector32Term::Variable(Variable(97));
        let mid = Bitvector32Term::Variable(Variable(98));
        let hi = Bitvector32Term::Variable(Variable(99));
        let x = Bitvector32Term::Variable(Variable(100));
        let accumulator = Variable(101);
        let item = Variable(102);
        let contribution = Bitvector32Term::if_then_else(
            ConditionTerm::equal(Bitvector32Term::Variable(item), x),
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(0),
        );
        let body = Bitvector32Term::add(Bitvector32Term::Variable(accumulator), contribution);
        let count = |start: Bitvector32Term, end: Bitvector32Term| {
            Bitvector32Term::range_fold(
                start,
                end,
                Bitvector32Term::Constant(0),
                accumulator,
                item,
                body.clone(),
            )
        };
        let whole = count(lo.clone(), hi.clone());
        let split = Bitvector32Term::add(count(lo, mid.clone()), count(mid, hi));

        assert!(Assumptions::new().proves(&Proposition::ConditionIs(
            ConditionTerm::equal(whole, split),
            true,
        )));
    }

    #[test]
    fn symbolic_store_invalidates_only_possible_aliasing_cells() {
        let i = Variable(81);
        let i_bits = Bitvector32Term::Variable(i);
        let concrete_cell = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let symbolic_cell = Pointer {
            block: "array".to_string(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(i_bits.clone()),
                byte_width: 4,
            },
        };
        let memory = CMemory::new()
            .with_block("array", 12)
            .store(concrete_cell.clone(), int32(42));

        let aliased = memory
            .without_possible_aliasing_cells(&symbolic_cell, &Assumptions::new())
            .store(symbolic_cell.clone(), int32(7));
        assert_eq!(aliased.known_value(&concrete_cell), None);

        let distinct_assumptions = Assumptions::new().assume_condition(
            ConditionTerm::equal(i_bits, Bitvector32Term::Constant(1)),
            false,
        );
        let distinct = memory
            .without_possible_aliasing_cells(&symbolic_cell, &distinct_assumptions)
            .store(symbolic_cell, int32(7));
        assert_eq!(distinct.known_value(&concrete_cell), Some(int32(42)));
    }

    #[test]
    fn assumptions_resolve_materialized_symbolic_memory_load_aliases() {
        let k = Variable(75);
        let k_bits = Bitvector32Term::Variable(k);
        let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
        let src_pointers = [0, 4, 8].map(|offset| Pointer {
            block: "src".to_string(),
            offset: PointerOffsetTerm::Constant(offset),
        });
        let symbolic_src = Pointer {
            block: "src".to_string(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(k_bits),
                byte_width: 4,
            },
        };
        let materialized_memory =
            src_pointers
                .iter()
                .cloned()
                .fold(base_memory.clone(), |memory, pointer| {
                    memory.store(
                        pointer.clone(),
                        int32(Bitvector32Term::MemoryLoad(
                            Box::new(base_memory.clone()),
                            Box::new(pointer),
                        )),
                    )
                });

        for (index, pointer) in src_pointers.into_iter().enumerate() {
            let assumptions = Assumptions::new()
                .assume_condition(
                    ConditionTerm::pointer_offset_equal(
                        symbolic_src.offset.clone(),
                        pointer.offset.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(k),
                        Bitvector32Term::Constant(index as u32),
                    ),
                    true,
                );

            assert!(assumptions.proves(&Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(Box::new(base_memory.clone()), Box::new(pointer)),
                    Bitvector32Term::MemoryLoad(
                        Box::new(materialized_memory.clone()),
                        Box::new(symbolic_src.clone()),
                    ),
                ),
                true,
            )));
        }
    }

    #[test]
    fn assumptions_prove_wrapped_materialized_load_branch_obligation() {
        let k = Variable(76);
        let k_bits = Bitvector32Term::Variable(k);
        let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
        let src_pointers = [0, 4, 8].map(|offset| Pointer {
            block: "src".to_string(),
            offset: PointerOffsetTerm::Constant(offset),
        });
        let symbolic_src = Pointer {
            block: "src".to_string(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(k_bits.clone()),
                byte_width: 4,
            },
        };
        let materialized_memory =
            src_pointers
                .iter()
                .cloned()
                .fold(base_memory.clone(), |memory, pointer| {
                    memory.store(
                        pointer.clone(),
                        int32(Bitvector32Term::MemoryLoad(
                            Box::new(base_memory.clone()),
                            Box::new(pointer),
                        )),
                    )
                });
        let body = Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(3)),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        Box::new(base_memory),
                        Box::new(src_pointers[1].clone()),
                    ),
                    Bitvector32Term::MemoryLoad(
                        Box::new(materialized_memory),
                        Box::new(symbolic_src.clone()),
                    ),
                ),
                true,
            )),
        );
        let proposition = Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(
                    symbolic_src.offset.clone(),
                    src_pointers[0].offset.clone(),
                ),
                false,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(k_bits.clone(), Bitvector32Term::Constant(0)),
                    false,
                )),
                Box::new(Proposition::Implies(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::pointer_offset_equal(
                            symbolic_src.offset,
                            src_pointers[1].offset.clone(),
                        ),
                        true,
                    )),
                    Box::new(Proposition::Implies(
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::equal(k_bits, Bitvector32Term::Constant(1)),
                            true,
                        )),
                        Box::new(Proposition::ForAll {
                            var: k,
                            sort: Sort::CInt32,
                            body: Box::new(body),
                        }),
                    )),
                )),
            )),
        );

        assert!(Assumptions::new().proves(&proposition));
    }

    #[test]
    fn assumptions_prove_copied_prefix_new_cell_obligation() {
        let i = Variable(82);
        let k = Variable(83);
        let i_bits = Bitvector32Term::Variable(i);
        let k_bits = Bitvector32Term::Variable(k);
        let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
        let src_pointers = [0, 4, 8].map(|offset| Pointer {
            block: "src".to_string(),
            offset: PointerOffsetTerm::Constant(offset),
        });
        let symbolic_src = Pointer {
            block: "src".to_string(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(k_bits.clone()),
                byte_width: 4,
            },
        };
        let materialized_memory =
            src_pointers
                .iter()
                .cloned()
                .fold(base_memory.clone(), |memory, pointer| {
                    memory.store(
                        pointer.clone(),
                        int32(Bitvector32Term::MemoryLoad(
                            Box::new(base_memory.clone()),
                            Box::new(pointer),
                        )),
                    )
                });
        let body = Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        k_bits.clone(),
                        Bitvector32Term::Add(
                            Box::new(i_bits.clone()),
                            Box::new(Bitvector32Term::Constant(1)),
                        ),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        Box::new(base_memory),
                        Box::new(src_pointers[1].clone()),
                    ),
                    Bitvector32Term::MemoryLoad(
                        Box::new(materialized_memory),
                        Box::new(symbolic_src.clone()),
                    ),
                ),
                true,
            )),
        );
        let proposition = Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(1)),
                true,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::pointer_offset_equal(
                        symbolic_src.offset,
                        PointerOffsetTerm::Int32Scaled {
                            value: Box::new(i_bits.clone()),
                            byte_width: 4,
                        },
                    ),
                    true,
                )),
                Box::new(Proposition::Implies(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::equal(k_bits, i_bits),
                        true,
                    )),
                    Box::new(Proposition::ForAll {
                        var: k,
                        sort: Sort::CInt32,
                        body: Box::new(body),
                    }),
                )),
            )),
        );

        assert!(Assumptions::new().proves(&proposition));
    }

    #[test]
    fn local_declaration_allocates_stack_object_for_address_of() {
        let local_pointer = Pointer {
            block: "local:x".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = CState::new();
        let statement = c_seq(
            c_declare("x", CType::Int32),
            c_seq(
                c_assign("x", c_int32_literal(5)),
                c_return(c_load(c_addr_of("x"))),
            ),
        );
        let final_state = CState::new().with_local("x", int32(5)).with_memory(
            CMemory::new()
                .with_block("local:x", 4)
                .store(local_pointer, int32(5)),
        );
        let theorem =
            prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
                .expect("local declaration/address-of should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state,
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(5),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn symbolic_execution_stops_without_needed_overflow_fact() {
        let left = Variable(20);
        let right = Variable(21);
        let state = CState::new()
            .with_local("left", int32(Bitvector32Term::Variable(left)))
            .with_local("right", int32(Bitvector32Term::Variable(right)));
        let statement = c_return(c_add(c_variable("left"), c_variable("right")));

        assert!(prove_symbolic_c_execution(state, statement, Assumptions::new()).is_none());
    }

    #[test]
    fn symbolic_execution_reports_branch_facts() {
        let a = Variable(24);
        let b = Variable(25);
        let a_bits = Bitvector32Term::Variable(a);
        let b_bits = Bitvector32Term::Variable(b);
        let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
        let state = c_max_state(int32(a_bits), int32(b_bits));
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), c_max_body(), Assumptions::new());

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].facts(),
            &[PathFact::condition(condition.clone(), true)]
        );
        assert_eq!(
            execution.paths()[0].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[0].theorem().proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition.clone(), true)),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement: c_max_body(),
                    outcome: CStatementOutcome::Return {
                        value: int32(Bitvector32Term::Variable(b)),
                        state: state.clone(),
                    },
                }),
            )
        );

        assert_eq!(
            execution.paths()[1].facts(),
            &[PathFact::condition(condition.clone(), false)]
        );
        assert_eq!(
            execution.paths()[1].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[1].theorem().proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, false)),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement: c_max_body(),
                    outcome: CStatementOutcome::Return {
                        value: int32(Bitvector32Term::Variable(a)),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn symbolic_execution_reports_overflow_facts() {
        let left = Variable(26);
        let right = Variable(27);
        let left_bits = Bitvector32Term::Variable(left);
        let right_bits = Bitvector32Term::Variable(right);
        let state = CState::new()
            .with_local("left", int32(left_bits.clone()))
            .with_local("right", int32(right_bits.clone()));
        let statement = c_return(c_add(c_variable("left"), c_variable("right")));
        let overflow = ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
        let execution =
            prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

        assert_eq!(execution.paths().len(), 2);
        assert_eq!(
            execution.paths()[0].facts(),
            &[PathFact::condition(overflow.clone(), false)]
        );
        assert_eq!(
            execution.paths()[0].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[0].theorem().proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(overflow.clone(), false)),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement: statement.clone(),
                    outcome: CStatementOutcome::Return {
                        value: int32(Bitvector32Term::Add(
                            Box::new(left_bits),
                            Box::new(right_bits)
                        )),
                        state: state.clone(),
                    },
                }),
            )
        );

        assert_eq!(
            execution.paths()[1].facts(),
            &[PathFact::condition(overflow.clone(), true)]
        );
        assert_eq!(
            execution.paths()[1].obligations(),
            &[] as &[ProofObligation]
        );
        assert_eq!(
            execution.paths()[1].theorem().proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(overflow, true)),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement,
                    outcome: CStatementOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow
                    ),
                }),
            )
        );
    }

    #[test]
    fn symbolic_execution_uses_no_overflow_fact() {
        let left = Variable(22);
        let right = Variable(23);
        let left_bits = Bitvector32Term::Variable(left);
        let right_bits = Bitvector32Term::Variable(right);
        let state = CState::new()
            .with_local("left", int32(left_bits.clone()))
            .with_local("right", int32(right_bits.clone()));
        let statement = c_return(c_add(c_variable("left"), c_variable("right")));
        let no_overflow =
            ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
        let assumptions = Assumptions::new().assume_condition(no_overflow.clone(), false);
        let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
            .expect("no-overflow fact should let symbolic add execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(no_overflow, false)),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement,
                    outcome: CStatementOutcome::Return {
                        value: int32(Bitvector32Term::Add(
                            Box::new(left_bits),
                            Box::new(right_bits)
                        )),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn symbolic_increment_uses_int_max_bound_to_rule_out_overflow() {
        let x = Variable(65);
        let x_bits = Bitvector32Term::Variable(x);
        let state = CState::new().with_local("x", int32(x_bits.clone()));
        let statement = c_return(c_add(c_variable("x"), c_int32_literal(1)));
        let x_lt_int_max = ConditionTerm::signed_less_than(
            x_bits.clone(),
            Bitvector32Term::Constant(i32::MAX as u32),
        );
        let assumptions = Assumptions::new().assume_condition(x_lt_int_max.clone(), true);
        let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
            .expect("x < INT_MAX should prove x + 1 does not overflow");

        assert_eq!(
            theorem.proposition(),
            &Proposition::Implies(
                Box::new(Proposition::ConditionIs(x_lt_int_max, true)),
                Box::new(Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement,
                    outcome: CStatementOutcome::Return {
                        value: int32(Bitvector32Term::Add(
                            Box::new(x_bits),
                            Box::new(Bitvector32Term::Constant(1)),
                        )),
                        state,
                    },
                }),
            )
        );
    }

    #[test]
    fn pointer_store_through_local_address_updates_named_lvalue() {
        let local_pointer = Pointer {
            block: "local:x".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let statement = c_seq(
            c_declare("x", CType::Int32),
            c_seq(
                c_store(c_addr_of("x"), c_int32_literal(5)),
                c_return(c_variable("x")),
            ),
        );
        let final_state = CState::new().with_local("x", int32(5)).with_memory(
            CMemory::new()
                .with_block("local:x", 4)
                .store(local_pointer, int32(5)),
        );
        let theorem =
            prove_symbolic_c_execution(CState::new(), statement.clone(), Assumptions::new())
                .expect("pointer store through local address should execute");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CStatementExecutes {
                state: CState::new(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(5),
                    state: final_state,
                },
            }
        );
    }

    #[test]
    fn memory_load_store_are_native_theorems() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let value = int32(7);
        let theorem =
            prove_memory_load_after_store_same(CMemory::new(), pointer.clone(), value.clone());

        assert_eq!(
            theorem.proposition(),
            &Proposition::CMemoryLoads {
                memory: CMemory::new().store(pointer.clone(), value.clone()),
                pointer,
                outcome: CExpressionOutcome::Value(value),
            }
        );
    }

    #[test]
    fn store_preserves_distinct_memory_cell_frame() {
        let stored_pointer = Pointer {
            block: "left".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let loaded_pointer = Pointer {
            block: "right".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().store(loaded_pointer.clone(), int32(42));
        let theorem = prove_memory_load_after_store_other(
            memory.clone(),
            stored_pointer.clone(),
            int32(9),
            loaded_pointer.clone(),
        )
        .expect("store to distinct pointer should preserve loaded cell");

        assert_eq!(
            theorem.proposition(),
            &Proposition::CMemoryLoads {
                memory: memory.store(stored_pointer, int32(9)),
                pointer: loaded_pointer,
                outcome: CExpressionOutcome::Value(int32(42)),
            }
        );
    }

    #[test]
    fn missing_memory_load_is_native_undefined_behavior() {
        let pointer = Pointer {
            block: "block".to_string(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let theorem = prove_memory_load(CMemory::new(), pointer.clone());

        assert_eq!(
            theorem.proposition(),
            &Proposition::CMemoryLoads {
                memory: CMemory::new(),
                pointer,
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            }
        );
    }
}
