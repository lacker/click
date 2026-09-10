//! Structural index keys for persistent checked proof facts.
//!
//! Snapshot-blind keys select a small set of potentially transportable facts.
//! A key match is never proof authority: the checked snapshot bridge still
//! validates every selected candidate.

use crate::kernel::{
    AlgebraicTerm, IntegerComparisonOperator, IntegerTerm, MachineIntegerType, Sort,
};
use crate::kernel::{
    Bitvector32Term, CComparisonOperator, CFloatBinaryOperator, CFloatClassification,
    CFloatCondition, CMemoryRange, CResource, ConditionTerm, Pointer, PointerBlock,
    PointerOffsetTerm, Proposition, Variable,
};
use num_bigint::BigInt;
use std::collections::BTreeMap;
use std::collections::HashMap;

#[cfg(test)]
thread_local! {
    static ALPHA_PROPOSITION_KEY_VISITS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
pub(crate) fn reset_alpha_proposition_key_visits() {
    ALPHA_PROPOSITION_KEY_VISITS.with(|visits| visits.set(0));
}

#[cfg(test)]
pub(crate) fn alpha_proposition_key_visits() -> usize {
    ALPHA_PROPOSITION_KEY_VISITS.with(std::cell::Cell::get)
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum SnapshotBlindPropositionKey {
    Condition(SnapshotBlindConditionKey, bool),
    Implies(Box<Self>, Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    MemorySeparate(
        Box<SnapshotBlindMemoryRangeKey>,
        Box<SnapshotBlindMemoryRangeKey>,
    ),
    Exact(Proposition),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct SnapshotBlindMemoryRangeKey {
    block: PointerBlock,
    offset: SnapshotBlindPointerOffsetKey,
    start: SnapshotBlindBitvectorKey,
    end: SnapshotBlindBitvectorKey,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum SnapshotBlindConditionKey {
    AlgebraicEqual(Box<AlgebraicTerm>, Box<AlgebraicTerm>),
    Constant(bool),
    Variable(Variable),
    SignedLessThan(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    SignedLessEqual(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    SignedGreaterThan(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    SignedGreaterEqual(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    Equal(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    AddOverflows(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    SubtractOverflows(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    MultiplyOverflows(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    DivideOverflows(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    ShiftLeftOverflows(SnapshotBlindBitvectorKey, SnapshotBlindBitvectorKey),
    Float32(SnapshotBlindFloatConditionKey),
    Float64(SnapshotBlindFloatConditionKey),
    PointerOffsetEqual(SnapshotBlindPointerOffsetKey, SnapshotBlindPointerOffsetKey),
    PointerEqual(SnapshotBlindPointerKey, SnapshotBlindPointerKey),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum SnapshotBlindFloatConditionKey {
    Comparison {
        operator: CComparisonOperator,
        left: SnapshotBlindBitvectorKey,
        right: SnapshotBlindBitvectorKey,
    },
    Classification {
        classification: CFloatClassification,
        value: SnapshotBlindBitvectorKey,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum SnapshotBlindBitvectorKey {
    Load(Box<SnapshotBlindPointerKey>),
    Add(Box<Self>, Box<Self>),
    Subtract(Box<Self>, Box<Self>),
    Multiply(Box<Self>, Box<Self>),
    Exact(Bitvector32Term),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct SnapshotBlindPointerKey {
    block: PointerBlock,
    offset: Box<SnapshotBlindPointerOffsetKey>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum SnapshotBlindPointerOffsetKey {
    Add(Box<Self>, Box<Self>),
    Int32Scaled {
        value: SnapshotBlindBitvectorKey,
        byte_width: i64,
    },
    Int64Scaled {
        value: SnapshotBlindBitvectorKey,
        byte_width: i64,
        unsigned: bool,
    },
    Exact(PointerOffsetTerm),
}

impl SnapshotBlindPropositionKey {
    pub(crate) fn forgets_a_snapshot(&self) -> bool {
        match self {
            Self::Condition(condition, _) => condition.forgets_a_snapshot(),
            Self::Implies(left, right) | Self::And(left, right) | Self::Or(left, right) => {
                left.forgets_a_snapshot() || right.forgets_a_snapshot()
            }
            Self::Not(body) => body.forgets_a_snapshot(),
            Self::MemorySeparate(left, right) => {
                let side = |key: &SnapshotBlindMemoryRangeKey| {
                    key.offset.forgets_a_snapshot()
                        || key.start.forgets_a_snapshot()
                        || key.end.forgets_a_snapshot()
                };
                side(left) || side(right)
            }
            Self::Exact(_) => false,
        }
    }
}

impl SnapshotBlindConditionKey {
    fn forgets_a_snapshot(&self) -> bool {
        match self {
            Self::AlgebraicEqual(_, _) => false,
            Self::SignedLessThan(left, right)
            | Self::SignedLessEqual(left, right)
            | Self::SignedGreaterThan(left, right)
            | Self::SignedGreaterEqual(left, right)
            | Self::Equal(left, right)
            | Self::AddOverflows(left, right)
            | Self::SubtractOverflows(left, right)
            | Self::MultiplyOverflows(left, right)
            | Self::DivideOverflows(left, right)
            | Self::ShiftLeftOverflows(left, right) => {
                left.forgets_a_snapshot() || right.forgets_a_snapshot()
            }
            Self::Float32(condition) | Self::Float64(condition) => condition.forgets_a_snapshot(),
            Self::PointerOffsetEqual(left, right) => {
                left.forgets_a_snapshot() || right.forgets_a_snapshot()
            }
            Self::PointerEqual(left, right) => {
                left.forgets_a_snapshot() || right.forgets_a_snapshot()
            }
            Self::Constant(_) | Self::Variable(_) => false,
        }
    }
}

impl SnapshotBlindFloatConditionKey {
    fn forgets_a_snapshot(&self) -> bool {
        match self {
            Self::Comparison { left, right, .. } => {
                left.forgets_a_snapshot() || right.forgets_a_snapshot()
            }
            Self::Classification { value, .. } => value.forgets_a_snapshot(),
        }
    }
}

impl SnapshotBlindBitvectorKey {
    fn forgets_a_snapshot(&self) -> bool {
        match self {
            Self::Load(_) => true,
            Self::Add(left, right) | Self::Subtract(left, right) | Self::Multiply(left, right) => {
                left.forgets_a_snapshot() || right.forgets_a_snapshot()
            }
            Self::Exact(_) => false,
        }
    }
}

impl SnapshotBlindPointerKey {
    fn forgets_a_snapshot(&self) -> bool {
        self.offset.forgets_a_snapshot()
    }
}

impl SnapshotBlindPointerOffsetKey {
    fn forgets_a_snapshot(&self) -> bool {
        match self {
            Self::Add(left, right) => left.forgets_a_snapshot() || right.forgets_a_snapshot(),
            Self::Int32Scaled { value, .. } | Self::Int64Scaled { value, .. } => {
                value.forgets_a_snapshot()
            }
            Self::Exact(_) => false,
        }
    }
}

pub(crate) fn snapshot_blind_proposition_key(
    proposition: &Proposition,
) -> SnapshotBlindPropositionKey {
    match proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerLessThan(_, _)
            | ConditionTerm::IntegerLessEqual(_, _)
            | ConditionTerm::IntegerGreaterThan(_, _)
            | ConditionTerm::IntegerGreaterEqual(_, _)
            | ConditionTerm::IntegerEqual(_, _)
            | ConditionTerm::IntegerNotEqual(_, _),
            _,
        ) => SnapshotBlindPropositionKey::Exact(proposition.clone()),
        Proposition::ConditionIs(condition, value) => {
            SnapshotBlindPropositionKey::Condition(snapshot_blind_condition_key(condition), *value)
        }
        Proposition::Implies(left, right) => SnapshotBlindPropositionKey::Implies(
            Box::new(snapshot_blind_proposition_key(left)),
            Box::new(snapshot_blind_proposition_key(right)),
        ),
        Proposition::And(left, right) => SnapshotBlindPropositionKey::And(
            Box::new(snapshot_blind_proposition_key(left)),
            Box::new(snapshot_blind_proposition_key(right)),
        ),
        Proposition::Or(left, right) => SnapshotBlindPropositionKey::Or(
            Box::new(snapshot_blind_proposition_key(left)),
            Box::new(snapshot_blind_proposition_key(right)),
        ),
        Proposition::Not(body) => {
            SnapshotBlindPropositionKey::Not(Box::new(snapshot_blind_proposition_key(body)))
        }
        Proposition::CResourceSeparate {
            left: CResource::Memory(left),
            right: CResource::Memory(right),
        } => SnapshotBlindPropositionKey::MemorySeparate(
            snapshot_blind_memory_range_key(left),
            snapshot_blind_memory_range_key(right),
        ),
        proposition => SnapshotBlindPropositionKey::Exact(proposition.clone()),
    }
}

fn snapshot_blind_memory_range_key(range: &CMemoryRange) -> Box<SnapshotBlindMemoryRangeKey> {
    Box::new(SnapshotBlindMemoryRangeKey {
        block: range.base().block.clone(),
        offset: snapshot_blind_pointer_offset_key(&range.base().offset),
        start: snapshot_blind_bitvector_key(range.start()),
        end: snapshot_blind_bitvector_key(range.end()),
    })
}

fn snapshot_blind_condition_key(condition: &ConditionTerm) -> SnapshotBlindConditionKey {
    let terms = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            snapshot_blind_bitvector_key(left),
            snapshot_blind_bitvector_key(right),
        )
    };
    match condition {
        ConditionTerm::Constant(value) => SnapshotBlindConditionKey::Constant(*value),
        ConditionTerm::AlgebraicEqual(left, right) => {
            SnapshotBlindConditionKey::AlgebraicEqual(left.clone(), right.clone())
        }
        ConditionTerm::Variable(variable) => SnapshotBlindConditionKey::Variable(*variable),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SignedLessThan(left, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::Equal(left, right)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::AddOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SubtractOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::MultiplyOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::DivideOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::ShiftLeftOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SignedLessThan(left, right)
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector64Equal(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::Equal(left, right)
        }
        ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::AddOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::SubtractOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::MultiplyOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::DivideOverflows(left, right)
        }
        ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            let (left, right) = terms(left, right);
            SnapshotBlindConditionKey::ShiftLeftOverflows(left, right)
        }
        ConditionTerm::Float32(float_condition) => {
            SnapshotBlindConditionKey::Float32(snapshot_blind_float_condition_key(float_condition))
        }
        ConditionTerm::Float64(float_condition) => {
            SnapshotBlindConditionKey::Float64(snapshot_blind_float_condition_key(float_condition))
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            SnapshotBlindConditionKey::PointerOffsetEqual(
                snapshot_blind_pointer_offset_key(left),
                snapshot_blind_pointer_offset_key(right),
            )
        }
        ConditionTerm::PointerEqual(left, right) => SnapshotBlindConditionKey::PointerEqual(
            snapshot_blind_pointer_key(left),
            snapshot_blind_pointer_key(right),
        ),
        ConditionTerm::IntegerLessThan(_, _)
        | ConditionTerm::IntegerLessEqual(_, _)
        | ConditionTerm::IntegerGreaterThan(_, _)
        | ConditionTerm::IntegerGreaterEqual(_, _)
        | ConditionTerm::IntegerEqual(_, _)
        | ConditionTerm::IntegerNotEqual(_, _) => {
            unreachable!("integer conditions use the exact proposition index")
        }
    }
}

fn snapshot_blind_float_condition_key(
    condition: &CFloatCondition,
) -> SnapshotBlindFloatConditionKey {
    match condition {
        CFloatCondition::Comparison {
            operator,
            left,
            right,
        } => SnapshotBlindFloatConditionKey::Comparison {
            operator: *operator,
            left: snapshot_blind_bitvector_key(left),
            right: snapshot_blind_bitvector_key(right),
        },
        CFloatCondition::Classification {
            classification,
            value,
        } => SnapshotBlindFloatConditionKey::Classification {
            classification: *classification,
            value: snapshot_blind_bitvector_key(value),
        },
    }
}

fn snapshot_blind_bitvector_key(term: &Bitvector32Term) -> SnapshotBlindBitvectorKey {
    match term {
        Bitvector32Term::MemoryLoad(_, pointer) => {
            SnapshotBlindBitvectorKey::Load(Box::new(snapshot_blind_pointer_key(pointer)))
        }
        Bitvector32Term::Variable(variable) if crate::kernel::is_load_variable(variable) => {
            match crate::kernel::registered_load_for_variable(variable) {
                Some((_, pointer)) => {
                    SnapshotBlindBitvectorKey::Load(Box::new(snapshot_blind_pointer_key(&pointer)))
                }
                None => SnapshotBlindBitvectorKey::Exact(term.clone()),
            }
        }
        Bitvector32Term::Add(left, right) => SnapshotBlindBitvectorKey::Add(
            Box::new(snapshot_blind_bitvector_key(left)),
            Box::new(snapshot_blind_bitvector_key(right)),
        ),
        Bitvector32Term::Subtract(left, right) => SnapshotBlindBitvectorKey::Subtract(
            Box::new(snapshot_blind_bitvector_key(left)),
            Box::new(snapshot_blind_bitvector_key(right)),
        ),
        Bitvector32Term::Multiply(left, right) => SnapshotBlindBitvectorKey::Multiply(
            Box::new(snapshot_blind_bitvector_key(left)),
            Box::new(snapshot_blind_bitvector_key(right)),
        ),
        term => SnapshotBlindBitvectorKey::Exact(term.clone()),
    }
}

fn snapshot_blind_pointer_key(pointer: &Pointer) -> SnapshotBlindPointerKey {
    SnapshotBlindPointerKey {
        block: pointer.block.clone(),
        offset: Box::new(snapshot_blind_pointer_offset_key(&pointer.offset)),
    }
}

fn snapshot_blind_pointer_offset_key(offset: &PointerOffsetTerm) -> SnapshotBlindPointerOffsetKey {
    match offset {
        PointerOffsetTerm::Add(left, right) => SnapshotBlindPointerOffsetKey::Add(
            Box::new(snapshot_blind_pointer_offset_key(left)),
            Box::new(snapshot_blind_pointer_offset_key(right)),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            SnapshotBlindPointerOffsetKey::Int32Scaled {
                value: snapshot_blind_bitvector_key(value),
                byte_width: *byte_width,
            }
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => SnapshotBlindPointerOffsetKey::Int64Scaled {
            value: snapshot_blind_bitvector_key(value),
            byte_width: *byte_width,
            unsigned: *unsigned,
        },
        offset => SnapshotBlindPointerOffsetKey::Exact(offset.clone()),
    }
}

/// Alpha-invariant key for the quantified logical/condition fragment used by
/// checked premises. Bound variables use structural ordinals; free variables
/// retain their kernel identities, and memory snapshots in loads are omitted.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct QuantifiedEquivalenceKey(AlphaPropositionKey);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AlphaPropositionKey {
    Condition(AlphaConditionKey, bool),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    Implies(Box<Self>, Box<Self>),
    ForAll(Sort, Box<Self>),
    Exists(Sort, Box<Self>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaVariableKey {
    Bound(usize),
    Free(Variable),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaBitvectorBinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    UnsignedDivide,
    Remainder,
    UnsignedRemainder,
    ShiftLeft,
    ArithmeticShiftRight,
    LogicalShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    Int64Add,
    Int64Subtract,
    Int64Multiply,
    Int64Divide,
    Int64Remainder,
    Int64ShiftLeft,
    Int64ArithmeticShiftRight,
    Int64BitwiseAnd,
    Int64BitwiseOr,
    Int64BitwiseXor,
    UInt64Add,
    UInt64Subtract,
    UInt64Multiply,
    UInt64Divide,
    UInt64Remainder,
    UInt64ShiftLeft,
    UInt64LogicalShiftRight,
    UInt64BitwiseAnd,
    UInt64BitwiseOr,
    UInt64BitwiseXor,
    Float32(CFloatBinaryOperator),
    Float64(CFloatBinaryOperator),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaBitvectorKey {
    Constant(u32),
    Int64Constant(i64),
    UInt64Constant(u64),
    Variable(AlphaVariableKey),
    Binary(AlphaBitvectorBinaryOp, Box<Self>, Box<Self>),
    BitwiseNot(Box<Self>),
    Int64BitwiseNot(Box<Self>),
    UInt64BitwiseNot(Box<Self>),
    Float32Negate(Box<Self>),
    Float64Negate(Box<Self>),
    If {
        condition: Box<AlphaConditionKey>,
        then_term: Box<Self>,
        else_term: Box<Self>,
    },
    RangeFold {
        start: Box<Self>,
        end: Box<Self>,
        initial: Box<Self>,
        body: Box<Self>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<Self>,
    },
    Load(Box<AlphaPointerKey>),
    Address(Box<AlphaPointerKey>),
    Int64From32(Box<Self>),
    UInt64From32(Box<Self>),
    UInt32From64(Box<Self>),
    Int64FromUInt32(Box<Self>),
    UInt64FromInt32(Box<Self>),
    UInt64FromInt64(Box<Self>),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPointerOffsetKey {
    Constant(i64),
    Variable(AlphaVariableKey),
    Add(Box<Self>, Box<Self>),
    Int32Scaled {
        value: Box<AlphaBitvectorKey>,
        byte_width: i64,
    },
    Int64Scaled {
        value: Box<AlphaBitvectorKey>,
        byte_width: i64,
        unsigned: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPointerBlockKey {
    Concrete(String),
    StringLiteral { identity: String, bytes: Vec<u8> },
    Function(String),
    FunctionSymbolic(AlphaVariableKey),
    ExternalArgument,
    Symbolic(AlphaVariableKey),
    Heap(u64),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct AlphaPointerKey {
    block: AlphaPointerBlockKey,
    offset: AlphaPointerOffsetKey,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaConditionBinaryOp {
    SignedLessThan,
    SignedLessEqual,
    SignedGreaterThan,
    SignedGreaterEqual,
    Equal,
    AddOverflows,
    SubtractOverflows,
    MultiplyOverflows,
    DivideOverflows,
    ShiftLeftOverflows,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaConditionKey {
    Constant(bool),
    Variable(AlphaVariableKey),
    Binary(AlphaConditionBinaryOp, AlphaBitvectorKey, AlphaBitvectorKey),
    PointerOffsetEqual(AlphaPointerOffsetKey, AlphaPointerOffsetKey),
    PointerEqual(AlphaPointerKey, AlphaPointerKey),
    IntegerComparison(IntegerComparisonOperator, AlphaIntegerKey, AlphaIntegerKey),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct AlphaIntegerKey {
    nodes: Vec<AlphaIntegerNode>,
    root: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaIntegerNode {
    Constant(BigInt),
    Variable(AlphaVariableKey),
    Machine(MachineIntegerType, AlphaBitvectorKey),
    Negate(usize),
    Binary {
        operator: IntegerTermBinaryOp,
        left: usize,
        right: usize,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum IntegerTermBinaryOp {
    Add,
    Subtract,
    Multiply,
}

fn alpha_integer_key(
    term: &IntegerTerm,
    bindings: &mut BTreeMap<Variable, usize>,
) -> Option<AlphaIntegerKey> {
    let mut nodes = Vec::new();
    let mut memo = HashMap::new();
    let root = alpha_integer_node(&term.clone().into(), bindings, &mut memo, &mut nodes)?;
    Some(AlphaIntegerKey { nodes, root })
}

fn alpha_integer_node(
    shared: &crate::kernel::SharedIntegerTerm,
    bindings: &mut BTreeMap<Variable, usize>,
    memo: &mut HashMap<u64, usize>,
    nodes: &mut Vec<AlphaIntegerNode>,
) -> Option<usize> {
    if let Some(index) = memo.get(&shared.id()) {
        return Some(*index);
    }
    let term = shared.as_ref();
    crate::instrumentation::record_deterministic_work(1);
    let node = match term {
        IntegerTerm::Constant(value) => {
            crate::instrumentation::record_deterministic_work(value.bits() as usize + 1);
            AlphaIntegerNode::Constant(value.clone())
        }
        IntegerTerm::Variable(variable) => {
            AlphaIntegerNode::Variable(alpha_variable_key::<false>(*variable, bindings)?)
        }
        IntegerTerm::Machine(value) => AlphaIntegerNode::Machine(
            value.ty(),
            alpha_bitvector_key::<false>(value.value(), bindings, &mut 0)?,
        ),
        IntegerTerm::Negate(value) => {
            AlphaIntegerNode::Negate(alpha_integer_node(value, bindings, memo, nodes)?)
        }
        IntegerTerm::Add(left, right) => AlphaIntegerNode::Binary {
            operator: IntegerTermBinaryOp::Add,
            left: alpha_integer_node(left, bindings, memo, nodes)?,
            right: alpha_integer_node(right, bindings, memo, nodes)?,
        },
        IntegerTerm::Subtract(left, right) => AlphaIntegerNode::Binary {
            operator: IntegerTermBinaryOp::Subtract,
            left: alpha_integer_node(left, bindings, memo, nodes)?,
            right: alpha_integer_node(right, bindings, memo, nodes)?,
        },
        IntegerTerm::Multiply(left, right) => AlphaIntegerNode::Binary {
            operator: IntegerTermBinaryOp::Multiply,
            left: alpha_integer_node(left, bindings, memo, nodes)?,
            right: alpha_integer_node(right, bindings, memo, nodes)?,
        },
    };
    let index = nodes.len();
    nodes.push(node);
    memo.insert(shared.id(), index);
    Some(index)
}

fn alpha_variable_key<const ALLOW_LOADS: bool>(
    variable: Variable,
    bindings: &BTreeMap<Variable, usize>,
) -> Option<AlphaVariableKey> {
    if !ALLOW_LOADS && crate::kernel::is_load_variable(&variable) {
        return None;
    }
    Some(
        bindings
            .get(&variable)
            .copied()
            .map(AlphaVariableKey::Bound)
            .unwrap_or(AlphaVariableKey::Free(variable)),
    )
}

fn alpha_pointer_offset_key<const ALLOW_LOADS: bool>(
    offset: &PointerOffsetTerm,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaPointerOffsetKey> {
    crate::instrumentation::record_deterministic_work(1);
    Some(match offset {
        PointerOffsetTerm::Constant(value) => AlphaPointerOffsetKey::Constant(*value),
        PointerOffsetTerm::Variable(variable) => {
            AlphaPointerOffsetKey::Variable(alpha_variable_key::<ALLOW_LOADS>(*variable, bindings)?)
        }
        PointerOffsetTerm::Add(left, right) => AlphaPointerOffsetKey::Add(
            Box::new(alpha_pointer_offset_key::<ALLOW_LOADS>(
                left,
                bindings,
                next_binder,
            )?),
            Box::new(alpha_pointer_offset_key::<ALLOW_LOADS>(
                right,
                bindings,
                next_binder,
            )?),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            AlphaPointerOffsetKey::Int32Scaled {
                value: Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                    value,
                    bindings,
                    next_binder,
                )?),
                byte_width: *byte_width,
            }
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => AlphaPointerOffsetKey::Int64Scaled {
            value: Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                value,
                bindings,
                next_binder,
            )?),
            byte_width: *byte_width,
            unsigned: *unsigned,
        },
    })
}

fn alpha_pointer_key<const ALLOW_LOADS: bool>(
    pointer: &Pointer,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaPointerKey> {
    crate::instrumentation::record_deterministic_work(1);
    let block = match &pointer.block {
        PointerBlock::Concrete(name) => AlphaPointerBlockKey::Concrete(name.clone()),
        PointerBlock::StringLiteral { identity, bytes } => AlphaPointerBlockKey::StringLiteral {
            identity: identity.clone(),
            bytes: bytes.clone(),
        },
        PointerBlock::Function(name) => AlphaPointerBlockKey::Function(name.clone()),
        PointerBlock::FunctionSymbolic(variable) => AlphaPointerBlockKey::FunctionSymbolic(
            alpha_variable_key::<ALLOW_LOADS>(*variable, bindings)?,
        ),
        PointerBlock::ExternalArgument => AlphaPointerBlockKey::ExternalArgument,
        PointerBlock::Symbolic(variable) => {
            AlphaPointerBlockKey::Symbolic(alpha_variable_key::<ALLOW_LOADS>(*variable, bindings)?)
        }
        PointerBlock::Heap(identity) => AlphaPointerBlockKey::Heap(*identity),
    };
    Some(AlphaPointerKey {
        block,
        offset: alpha_pointer_offset_key::<ALLOW_LOADS>(&pointer.offset, bindings, next_binder)?,
    })
}

fn alpha_bitvector_key<const ALLOW_LOADS: bool>(
    term: &Bitvector32Term,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    crate::instrumentation::record_deterministic_work(1);
    // Load variables hide snapshots too: their binders cannot be treated as
    // opaque free variables by the memory-free structural authority.
    if !ALLOW_LOADS
        && (matches!(term, Bitvector32Term::MemoryLoad(..))
            || matches!(term, Bitvector32Term::Variable(variable) if crate::kernel::is_load_variable(variable)))
    {
        return None;
    }
    let mut binary =
        |operator, left: &Bitvector32Term, right: &Bitvector32Term| -> Option<AlphaBitvectorKey> {
            Some(AlphaBitvectorKey::Binary(
                operator,
                Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                    left,
                    bindings,
                    next_binder,
                )?),
                Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                    right,
                    bindings,
                    next_binder,
                )?),
            ))
        };
    Some(match term {
        Bitvector32Term::Constant(value) => AlphaBitvectorKey::Constant(*value),
        Bitvector32Term::Int64Constant(value) => AlphaBitvectorKey::Int64Constant(*value),
        Bitvector32Term::UInt64Constant(value) => AlphaBitvectorKey::UInt64Constant(*value),
        Bitvector32Term::Variable(variable) => {
            match crate::kernel::is_load_variable(variable)
                .then(|| crate::kernel::registered_load_for_variable(variable))
                .flatten()
            {
                Some((_, pointer)) => {
                    AlphaBitvectorKey::Load(Box::new(alpha_pointer_key::<ALLOW_LOADS>(
                        &pointer,
                        bindings,
                        next_binder,
                    )?))
                }
                None => AlphaBitvectorKey::Variable(alpha_variable_key::<ALLOW_LOADS>(
                    *variable, bindings,
                )?),
            }
        }
        Bitvector32Term::Add(left, right) => binary(AlphaBitvectorBinaryOp::Add, left, right)?,
        Bitvector32Term::Subtract(left, right) => {
            binary(AlphaBitvectorBinaryOp::Subtract, left, right)?
        }
        Bitvector32Term::Multiply(left, right) => {
            binary(AlphaBitvectorBinaryOp::Multiply, left, right)?
        }
        Bitvector32Term::Divide(left, right) => {
            binary(AlphaBitvectorBinaryOp::Divide, left, right)?
        }
        Bitvector32Term::UnsignedDivide(left, right) => {
            binary(AlphaBitvectorBinaryOp::UnsignedDivide, left, right)?
        }
        Bitvector32Term::Remainder(left, right) => {
            binary(AlphaBitvectorBinaryOp::Remainder, left, right)?
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            binary(AlphaBitvectorBinaryOp::UnsignedRemainder, left, right)?
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            binary(AlphaBitvectorBinaryOp::ShiftLeft, left, right)?
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            binary(AlphaBitvectorBinaryOp::ArithmeticShiftRight, left, right)?
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            binary(AlphaBitvectorBinaryOp::LogicalShiftRight, left, right)?
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            binary(AlphaBitvectorBinaryOp::BitwiseAnd, left, right)?
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            binary(AlphaBitvectorBinaryOp::BitwiseOr, left, right)?
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            binary(AlphaBitvectorBinaryOp::BitwiseXor, left, right)?
        }
        Bitvector32Term::Int64Add(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64Add, left, right)?
        }
        Bitvector32Term::Int64Subtract(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64Subtract, left, right)?
        }
        Bitvector32Term::Int64Multiply(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64Multiply, left, right)?
        }
        Bitvector32Term::Int64Divide(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64Divide, left, right)?
        }
        Bitvector32Term::Int64Remainder(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64Remainder, left, right)?
        }
        Bitvector32Term::Int64ShiftLeft(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64ShiftLeft, left, right)?
        }
        Bitvector32Term::Int64ArithmeticShiftRight(left, right) => binary(
            AlphaBitvectorBinaryOp::Int64ArithmeticShiftRight,
            left,
            right,
        )?,
        Bitvector32Term::Int64BitwiseAnd(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64BitwiseAnd, left, right)?
        }
        Bitvector32Term::Int64BitwiseOr(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64BitwiseOr, left, right)?
        }
        Bitvector32Term::Int64BitwiseXor(left, right) => {
            binary(AlphaBitvectorBinaryOp::Int64BitwiseXor, left, right)?
        }
        Bitvector32Term::UInt64Add(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64Add, left, right)?
        }
        Bitvector32Term::UInt64Subtract(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64Subtract, left, right)?
        }
        Bitvector32Term::UInt64Multiply(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64Multiply, left, right)?
        }
        Bitvector32Term::UInt64Divide(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64Divide, left, right)?
        }
        Bitvector32Term::UInt64Remainder(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64Remainder, left, right)?
        }
        Bitvector32Term::UInt64ShiftLeft(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64ShiftLeft, left, right)?
        }
        Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64LogicalShiftRight, left, right)?
        }
        Bitvector32Term::UInt64BitwiseAnd(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64BitwiseAnd, left, right)?
        }
        Bitvector32Term::UInt64BitwiseOr(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64BitwiseOr, left, right)?
        }
        Bitvector32Term::UInt64BitwiseXor(left, right) => {
            binary(AlphaBitvectorBinaryOp::UInt64BitwiseXor, left, right)?
        }
        Bitvector32Term::Float32Binary {
            operator,
            left,
            right,
        } => binary(AlphaBitvectorBinaryOp::Float32(*operator), left, right)?,
        Bitvector32Term::Float64Binary {
            operator,
            left,
            right,
        } => binary(AlphaBitvectorBinaryOp::Float64(*operator), left, right)?,
        Bitvector32Term::BitwiseNot(body) => AlphaBitvectorKey::BitwiseNot(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(body, bindings, next_binder)?,
        )),
        Bitvector32Term::Int64BitwiseNot(body) => AlphaBitvectorKey::Int64BitwiseNot(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(body, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt64BitwiseNot(body) => AlphaBitvectorKey::UInt64BitwiseNot(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(body, bindings, next_binder)?,
        )),
        Bitvector32Term::Float32Negate(body) => AlphaBitvectorKey::Float32Negate(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(body, bindings, next_binder)?,
        )),
        Bitvector32Term::Float64Negate(body) => AlphaBitvectorKey::Float64Negate(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(body, bindings, next_binder)?,
        )),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => AlphaBitvectorKey::If {
            condition: Box::new(alpha_condition_key::<ALLOW_LOADS>(
                condition,
                bindings,
                next_binder,
            )?),
            then_term: Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                then_term,
                bindings,
                next_binder,
            )?),
            else_term: Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                else_term,
                bindings,
                next_binder,
            )?),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let start = Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                start,
                bindings,
                next_binder,
            )?);
            let end = Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                end,
                bindings,
                next_binder,
            )?);
            let initial = Box::new(alpha_bitvector_key::<ALLOW_LOADS>(
                initial,
                bindings,
                next_binder,
            )?);

            // Range-fold accumulator and item variables are binders just like
            // proposition quantifiers. Canonicalize their body under fresh
            // structural ordinals, then restore any enclosing binding so a
            // fold cannot change the meaning of a sibling term.
            let accumulator_ordinal = *next_binder;
            *next_binder += 1;
            let previous_accumulator = bindings.insert(*accumulator, accumulator_ordinal);
            let item_ordinal = *next_binder;
            *next_binder += 1;
            let previous_item = bindings.insert(*item, item_ordinal);
            let body = alpha_bitvector_key::<ALLOW_LOADS>(body, bindings, next_binder);
            if let Some(previous) = previous_item {
                bindings.insert(*item, previous);
            } else {
                bindings.remove(item);
            }
            if let Some(previous) = previous_accumulator {
                bindings.insert(*accumulator, previous);
            } else {
                bindings.remove(accumulator);
            }

            AlphaBitvectorKey::RangeFold {
                start,
                end,
                initial,
                body: Box::new(body?),
            }
        }
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            AlphaBitvectorKey::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        alpha_bitvector_key::<ALLOW_LOADS>(argument, bindings, next_binder)
                    })
                    .collect::<Option<Vec<_>>>()?,
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => return None,
        Bitvector32Term::MemoryLoad(_, pointer) => AlphaBitvectorKey::Load(Box::new(
            alpha_pointer_key::<ALLOW_LOADS>(pointer, bindings, next_binder)?,
        )),
        Bitvector32Term::PointerAddress(pointer) => AlphaBitvectorKey::Address(Box::new(
            alpha_pointer_key::<ALLOW_LOADS>(pointer, bindings, next_binder)?,
        )),
        Bitvector32Term::IntegerToMachine { .. } => return None,
        Bitvector32Term::Int64From32(value) => AlphaBitvectorKey::Int64From32(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(value, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt64From32(value) => AlphaBitvectorKey::UInt64From32(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(value, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt32From64(value) => AlphaBitvectorKey::UInt32From64(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(value, bindings, next_binder)?,
        )),
        Bitvector32Term::Int64FromUInt32(value) => AlphaBitvectorKey::Int64FromUInt32(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(value, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt64FromInt32(value) => AlphaBitvectorKey::UInt64FromInt32(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(value, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt64FromInt64(value) => AlphaBitvectorKey::UInt64FromInt64(Box::new(
            alpha_bitvector_key::<ALLOW_LOADS>(value, bindings, next_binder)?,
        )),
    })
}

fn alpha_condition_key<const ALLOW_LOADS: bool>(
    condition: &ConditionTerm,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaConditionKey> {
    crate::instrumentation::record_deterministic_work(1);
    let mut binary =
        |operator, left: &Bitvector32Term, right: &Bitvector32Term| -> Option<AlphaConditionKey> {
            Some(AlphaConditionKey::Binary(
                operator,
                alpha_bitvector_key::<ALLOW_LOADS>(left, bindings, next_binder)?,
                alpha_bitvector_key::<ALLOW_LOADS>(right, bindings, next_binder)?,
            ))
        };
    Some(match condition {
        ConditionTerm::Constant(value) => AlphaConditionKey::Constant(*value),
        ConditionTerm::Variable(variable) => {
            AlphaConditionKey::Variable(alpha_variable_key::<ALLOW_LOADS>(*variable, bindings)?)
        }
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            binary(AlphaConditionBinaryOp::SignedLessThan, left, right)?
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            binary(AlphaConditionBinaryOp::SignedLessEqual, left, right)?
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            binary(AlphaConditionBinaryOp::SignedGreaterThan, left, right)?
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            binary(AlphaConditionBinaryOp::SignedGreaterEqual, left, right)?
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            binary(AlphaConditionBinaryOp::Equal, left, right)?
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            binary(AlphaConditionBinaryOp::AddOverflows, left, right)?
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            binary(AlphaConditionBinaryOp::SubtractOverflows, left, right)?
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            binary(AlphaConditionBinaryOp::MultiplyOverflows, left, right)?
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            binary(AlphaConditionBinaryOp::DivideOverflows, left, right)?
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            binary(AlphaConditionBinaryOp::ShiftLeftOverflows, left, right)?
        }
        ConditionTerm::PointerOffsetEqual(left, right) => AlphaConditionKey::PointerOffsetEqual(
            alpha_pointer_offset_key::<ALLOW_LOADS>(left, bindings, next_binder)?,
            alpha_pointer_offset_key::<ALLOW_LOADS>(right, bindings, next_binder)?,
        ),
        ConditionTerm::PointerEqual(left, right) => AlphaConditionKey::PointerEqual(
            alpha_pointer_key::<ALLOW_LOADS>(left, bindings, next_binder)?,
            alpha_pointer_key::<ALLOW_LOADS>(right, bindings, next_binder)?,
        ),
        ConditionTerm::IntegerLessThan(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::LessThan,
            alpha_integer_key(left, bindings)?,
            alpha_integer_key(right, bindings)?,
        ),
        ConditionTerm::IntegerLessEqual(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::LessEqual,
            alpha_integer_key(left, bindings)?,
            alpha_integer_key(right, bindings)?,
        ),
        ConditionTerm::IntegerGreaterThan(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::GreaterThan,
            alpha_integer_key(left, bindings)?,
            alpha_integer_key(right, bindings)?,
        ),
        ConditionTerm::IntegerGreaterEqual(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::GreaterEqual,
            alpha_integer_key(left, bindings)?,
            alpha_integer_key(right, bindings)?,
        ),
        ConditionTerm::IntegerEqual(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::Equal,
            alpha_integer_key(left, bindings)?,
            alpha_integer_key(right, bindings)?,
        ),
        ConditionTerm::IntegerNotEqual(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::NotEqual,
            alpha_integer_key(left, bindings)?,
            alpha_integer_key(right, bindings)?,
        ),
        _ => return None,
    })
}

fn alpha_proposition_key<const ALLOW_LOADS: bool>(
    proposition: &Proposition,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaPropositionKey> {
    crate::instrumentation::record_deterministic_work(1);
    #[cfg(test)]
    ALPHA_PROPOSITION_KEY_VISITS.with(|visits| visits.set(visits.get() + 1));

    let binary = |left: &Proposition,
                  right: &Proposition,
                  bindings: &mut BTreeMap<Variable, usize>,
                  next_binder: &mut usize|
     -> Option<(Box<AlphaPropositionKey>, Box<AlphaPropositionKey>)> {
        let left = Box::new(alpha_proposition_key::<ALLOW_LOADS>(
            left,
            bindings,
            next_binder,
        )?);
        let right = Box::new(alpha_proposition_key::<ALLOW_LOADS>(
            right,
            bindings,
            next_binder,
        )?);
        Some((left, right))
    };
    Some(match proposition {
        Proposition::ConditionIs(condition, value) => AlphaPropositionKey::Condition(
            alpha_condition_key::<ALLOW_LOADS>(condition, bindings, next_binder)?,
            *value,
        ),
        Proposition::And(left, right) => {
            let (left, right) = binary(left, right, bindings, next_binder)?;
            AlphaPropositionKey::And(left, right)
        }
        Proposition::Or(left, right) => {
            let (left, right) = binary(left, right, bindings, next_binder)?;
            AlphaPropositionKey::Or(left, right)
        }
        Proposition::Implies(left, right) => {
            let (left, right) = binary(left, right, bindings, next_binder)?;
            AlphaPropositionKey::Implies(left, right)
        }
        Proposition::Not(body) => {
            AlphaPropositionKey::Not(Box::new(alpha_proposition_key::<ALLOW_LOADS>(
                body,
                bindings,
                next_binder,
            )?))
        }
        Proposition::ForAll { var, sort, body } => {
            let ordinal = *next_binder;
            *next_binder += 1;
            let prior = bindings.insert(*var, ordinal);
            let body = alpha_proposition_key::<ALLOW_LOADS>(body, bindings, next_binder);
            if let Some(prior) = prior {
                bindings.insert(*var, prior);
            } else {
                bindings.remove(var);
            }
            AlphaPropositionKey::ForAll(sort.clone(), Box::new(body?))
        }
        Proposition::Exists {
            var, sort, body, ..
        } => {
            let ordinal = *next_binder;
            *next_binder += 1;
            let prior = bindings.insert(*var, ordinal);
            let body = alpha_proposition_key::<ALLOW_LOADS>(body, bindings, next_binder);
            if let Some(prior) = prior {
                bindings.insert(*var, prior);
            } else {
                bindings.remove(var);
            }
            AlphaPropositionKey::Exists(sort.clone(), Box::new(body?))
        }
        _ => return None,
    })
}

pub(crate) fn quantified_equivalence_index_key(
    proposition: &Proposition,
) -> Option<QuantifiedEquivalenceKey> {
    if !matches!(
        proposition,
        Proposition::ForAll { .. } | Proposition::Exists { .. }
    ) {
        return None;
    }
    alpha_proposition_key::<true>(proposition, &mut BTreeMap::new(), &mut 0)
        .map(QuantifiedEquivalenceKey)
}

/// Exact alpha identity for the memory-free logical fragment. Unlike the
/// snapshot-blind selection key, this refuses all explicit and registered
/// loads; no snapshot contents or memory relations are inspected.
pub(crate) fn memory_free_quantified_key(
    proposition: &Proposition,
) -> Option<QuantifiedEquivalenceKey> {
    if !matches!(
        proposition,
        Proposition::ForAll { .. } | Proposition::Exists { .. }
    ) {
        return None;
    }
    alpha_proposition_key::<false>(proposition, &mut BTreeMap::new(), &mut 0)
        .map(QuantifiedEquivalenceKey)
}

#[cfg(test)]
mod integer_alpha_scaling_tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    #[test]
    fn alpha_integer_keys_compare_and_hash_linearly_for_shared_dags() {
        for depth in [8, 16, 32, 64] {
            let build = |variable| {
                let mut term = IntegerTerm::var(Variable(variable));
                for _ in 0..depth {
                    term = IntegerTerm::add(term.clone(), term.clone());
                }
                term
            };
            let left =
                alpha_integer_key(&build(70_000), &mut BTreeMap::from([(Variable(70_000), 0)]))
                    .unwrap();
            let right =
                alpha_integer_key(&build(71_000), &mut BTreeMap::from([(Variable(71_000), 0)]))
                    .unwrap();
            assert_eq!(left, right);
            let mut left_hash = DefaultHasher::new();
            let mut right_hash = DefaultHasher::new();
            left.hash(&mut left_hash);
            right.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());
        }
    }
}
