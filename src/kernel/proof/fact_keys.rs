//! Structural index keys for persistent checked proof facts.
//!
//! Snapshot-blind keys select a small set of potentially transportable facts.
//! A key match is never proof authority: the checked snapshot bridge still
//! validates every selected candidate.

use crate::kernel::{
    AlgebraicTerm, IntegerComparisonOperator, IntegerTerm, MachineIntegerType, SharedCMemory,
    SharedIntegerTerm, Sort,
};
use crate::kernel::{
    Bitvector32Term, CComparisonOperator, CFloatBinaryOperator, CFloatClassification,
    CFloatCondition, CMemoryRange, CResource, ConditionTerm, Pointer, PointerBlock,
    PointerOffsetTerm, Proposition, Variable,
};
use num_bigint::BigInt;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Weak};

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
/// checked premises. Bound variables use structural ordinals and free
/// variables retain their kernel identities. Raw bitvector loads outside a
/// loadability atom remain snapshot-blind on this selection path, while a
/// `CMemoryLoadable` atom retains the exact snapshot that is part of its
/// checked premise.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct QuantifiedEquivalenceKey(AlphaPropositionKey);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPropositionKey {
    Condition(AlphaConditionKey, bool),
    CMemoryLoadable {
        memory: AlphaSnapshotKey,
        base: AlphaPointerKey,
        bytes: AlphaBitvectorKey,
    },
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    Implies(Box<Self>, Box<Self>),
    ForAll(Sort, Box<Self>),
    Exists(Sort, Box<Self>),
}

#[derive(Clone)]
pub(crate) struct IntegerConditionAlphaKey {
    key: AlphaPropositionKey,
    work_units: usize,
}

impl fmt::Debug for IntegerConditionAlphaKey {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.key.fmt(formatter)
    }
}

impl PartialEq for IntegerConditionAlphaKey {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for IntegerConditionAlphaKey {}

impl PartialOrd for IntegerConditionAlphaKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IntegerConditionAlphaKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key.cmp(&other.key)
    }
}

impl Hash for IntegerConditionAlphaKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key.hash(state);
    }
}

impl IntegerConditionAlphaKey {
    pub(crate) fn fingerprint(&self) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    pub(crate) fn checked_fingerprint(&self) -> Option<u64> {
        if crate::instrumentation::deadline_exceeded_with_work(self.work_units) {
            return None;
        }
        Some(self.fingerprint())
    }

    pub(crate) fn checked_eq(&self, other: &Self) -> Option<bool> {
        if crate::instrumentation::deadline_exceeded_with_work(
            self.work_units.saturating_add(other.work_units),
        ) {
            return None;
        }
        Some(self == other)
    }
}

/// Backwards-compatible name for callers that only consume equality keys.
/// The underlying key is now shared by all root range-fold Integer
/// comparisons, so the persistent fact index can reuse the same checked,
/// snapshot-aware alpha boundary for equality and inequality premises.
pub(crate) type IntegerEqualityAlphaKey = IntegerConditionAlphaKey;

/// Alpha key used by the checked fact index for root range-fold Integer
/// comparison atoms.
///
/// Integer range-fold binders are canonicalized by a typed alpha environment.
/// Load-bearing C payloads retain their exact `SharedCMemory` identities, so
/// this index is authoritative only for comparisons whose loads name the same
/// snapshots. The entry point is deliberately narrow: only a true Integer
/// comparison with a range-fold operand at its root is eligible. Scalar
/// arithmetic comparisons remain on their existing exact/certificate path, so
/// indexing them cannot turn a sequence of growing arithmetic facts into
/// repeated deep walks.
pub(crate) fn integer_condition_alpha_key(
    proposition: &Proposition,
) -> Option<IntegerConditionAlphaKey> {
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    let (left, right) = match condition {
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => (left, right),
        _ => return None,
    };
    if !matches!(left.as_ref(), IntegerTerm::RangeFold { .. })
        && !matches!(right.as_ref(), IntegerTerm::RangeFold { .. })
    {
        return None;
    }
    snapshot_alpha_proposition_key(proposition)
        .map(|(key, work_units)| IntegerConditionAlphaKey { key, work_units })
}

/// Alpha key used by equality-specific callers. Keep this narrow wrapper so
/// equality normalization does not accidentally start accepting inequalities
/// as rewrite premises.
pub(crate) fn integer_equality_alpha_key(
    proposition: &Proposition,
) -> Option<IntegerEqualityAlphaKey> {
    matches!(
        proposition,
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(_, _), true)
    )
    .then(|| integer_condition_alpha_key(proposition))
    .flatten()
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
    RegisteredLoad(AlphaRegisteredLoadId),
    Address(Box<AlphaPointerKey>),
    IntegerToMachine(MachineIntegerType, AlphaIntegerKey),
    Int64From32(Box<Self>),
    UInt64From32(Box<Self>),
    UInt32From64(Box<Self>),
    Int64FromUInt32(Box<Self>),
    UInt64FromInt32(Box<Self>),
    UInt64FromInt64(Box<Self>),
}

/// O(1) identity for a retained memory snapshot.
///
/// A same-arena `(arena, id)` pair is the exact identity assigned by the
/// immutable memory arena.  Handles are retained so the identity cannot be
/// observed after its backing snapshot has been dropped.  Cross-arena
/// snapshots deliberately compare unequal: structural equality there would
/// scan the complete memory, so the exact authority falls back to its normal
/// proof path instead of consulting unrelated heap/history state.
#[derive(Clone)]
struct AlphaSnapshotKey {
    identity: (u32, u32),
    _snapshot: SharedCMemory,
}

impl AlphaSnapshotKey {
    fn new(snapshot: &SharedCMemory) -> Self {
        Self {
            identity: snapshot.arena_id(),
            _snapshot: snapshot.clone(),
        }
    }
}

impl fmt::Debug for AlphaSnapshotKey {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("AlphaSnapshotKey")
            .field(&self.identity)
            .finish()
    }
}

impl PartialEq for AlphaSnapshotKey {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}

impl Eq for AlphaSnapshotKey {}

impl PartialOrd for AlphaSnapshotKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AlphaSnapshotKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity.cmp(&other.identity)
    }
}

impl Hash for AlphaSnapshotKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPointerOffsetKey {
    Constant(i64),
    Variable(AlphaVariableKey),
    Add(Box<Self>, Box<Self>),
    RegisteredLoad(AlphaRegisteredLoadId),
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

/// A compact reference to one live canonical registered-load node. The node
/// owns its snapshot and its immediate pointer descriptor, while nested load
/// references own only their child nodes. This makes each key retain exactly
/// the reachable load DAG; the process-local interner stores weak records and
/// cannot keep unrelated snapshots alive after their keys are dropped.
#[derive(Clone)]
struct AlphaRegisteredLoadId(Arc<AlphaRegisteredLoadRecord>);

impl AlphaRegisteredLoadId {
    fn id(&self) -> u64 {
        self.0.id
    }
}

impl fmt::Debug for AlphaRegisteredLoadId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("AlphaRegisteredLoadId")
            .field(&self.id())
            .finish()
    }
}

impl PartialEq for AlphaRegisteredLoadId {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Eq for AlphaRegisteredLoadId {}

impl PartialOrd for AlphaRegisteredLoadId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AlphaRegisteredLoadId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id().cmp(&other.id())
    }
}

impl Hash for AlphaRegisteredLoadId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id().hash(state);
    }
}

struct AlphaRegisteredLoadRecord {
    id: u64,
    _interner: Arc<std::sync::Mutex<AlphaRegisteredLoadInterner>>,
    snapshot: AlphaSnapshotKey,
    pointer: AlphaPointerKey,
}

struct AlphaRegisteredLoadInterner {
    buckets: HashMap<u64, Vec<Weak<AlphaRegisteredLoadRecord>>>,
    cleanup: VecDeque<u64>,
}

impl AlphaRegisteredLoadInterner {
    fn clean_some(&mut self) -> Option<()> {
        let limit = self.cleanup.len().min(8);
        for _ in 0..limit {
            let Some(fingerprint) = self.cleanup.pop_front() else {
                break;
            };
            let Some(bucket) = self.buckets.get_mut(&fingerprint) else {
                continue;
            };
            if crate::instrumentation::deadline_exceeded_with_work(bucket.len().max(1)) {
                self.cleanup.push_front(fingerprint);
                return None;
            }
            bucket.retain(|candidate| candidate.strong_count() != 0);
            let bucket_is_empty = bucket.is_empty();
            if bucket_is_empty {
                self.buckets.remove(&fingerprint);
            } else {
                // Keep a live bucket on the bounded queue so a later drop of
                // its records is eventually observed even if no new query
                // hashes this fingerprint.
                self.cleanup.push_back(fingerprint);
            }
        }
        Some(())
    }
}

thread_local! {
    static ALPHA_REGISTERED_LOAD_INTERNER:
        std::cell::RefCell<Weak<std::sync::Mutex<AlphaRegisteredLoadInterner>>> =
            const { std::cell::RefCell::new(Weak::new()) };
}

static NEXT_ALPHA_REGISTERED_LOAD_ID: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(1);

fn alpha_registered_load_interner() -> Option<Arc<std::sync::Mutex<AlphaRegisteredLoadInterner>>> {
    ALPHA_REGISTERED_LOAD_INTERNER.with(|cell| {
        if let Some(interner) = cell.borrow().upgrade() {
            return Some(interner);
        }
        let interner = Arc::new(std::sync::Mutex::new(AlphaRegisteredLoadInterner {
            buckets: HashMap::new(),
            cleanup: VecDeque::new(),
        }));
        *cell.borrow_mut() = Arc::downgrade(&interner);
        Some(interner)
    })
}

fn alpha_registered_load_descriptor_fingerprint(
    snapshot: &AlphaSnapshotKey,
    pointer: &AlphaPointerKey,
) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    snapshot.hash(&mut hasher);
    pointer.hash(&mut hasher);
    hasher.finish()
}

fn intern_alpha_registered_load(
    interner: &Arc<std::sync::Mutex<AlphaRegisteredLoadInterner>>,
    snapshot: AlphaSnapshotKey,
    pointer: AlphaPointerKey,
) -> Option<AlphaRegisteredLoadId> {
    let fingerprint = alpha_registered_load_descriptor_fingerprint(&snapshot, &pointer);
    let mut interner_state = interner.lock().ok()?;
    interner_state.clean_some()?;
    let bucket = interner_state.buckets.entry(fingerprint).or_default();
    if crate::instrumentation::deadline_exceeded_with_work(bucket.len().max(1)) {
        return None;
    }
    bucket.retain(|candidate| candidate.strong_count() != 0);
    for candidate in bucket.iter() {
        let Some(record) = candidate.upgrade() else {
            continue;
        };
        if record.snapshot == snapshot && record.pointer == pointer {
            return Some(AlphaRegisteredLoadId(record));
        }
    }
    let id = NEXT_ALPHA_REGISTERED_LOAD_ID
        .fetch_update(
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
            |value| value.checked_add(1),
        )
        .ok()?;
    let record = Arc::new(AlphaRegisteredLoadRecord {
        id,
        _interner: interner.clone(),
        snapshot,
        pointer,
    });
    bucket.push(Arc::downgrade(&record));
    interner_state.cleanup.push_back(fingerprint);
    Some(AlphaRegisteredLoadId(record))
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

/// Opaque, exact alpha identity for one root Integer range fold.
///
/// The inner node graph retains carrier-aware binders and, in the snapshot
/// aware mode, the `SharedCMemory` handles named by load-bearing C payloads.
/// Consumers may hash or compare this value, but cannot inspect or rebuild its
/// structural representation on an arithmetic hot path.
#[derive(Clone)]
pub(crate) struct IntegerFoldAlphaKey {
    key: AlphaIntegerKey,
    work_units: usize,
}

impl fmt::Debug for IntegerFoldAlphaKey {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.key.fmt(formatter)
    }
}

impl PartialEq for IntegerFoldAlphaKey {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for IntegerFoldAlphaKey {}

impl PartialOrd for IntegerFoldAlphaKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IntegerFoldAlphaKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.key.cmp(&other.key)
    }
}

impl Hash for IntegerFoldAlphaKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key.hash(state);
    }
}

impl IntegerFoldAlphaKey {
    pub(crate) fn fingerprint(&self) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }

    pub(crate) fn checked_fingerprint(&self) -> Option<u64> {
        if crate::instrumentation::deadline_exceeded_with_work(self.work_units) {
            return None;
        }
        Some(self.fingerprint())
    }

    pub(crate) fn checked_eq(&self, other: &Self) -> Option<bool> {
        if crate::instrumentation::deadline_exceeded_with_work(
            self.work_units.saturating_add(other.work_units),
        ) {
            return None;
        }
        Some(self == other)
    }
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
    RangeFold {
        index: AlphaIntegerRangeIndex,
        initial: usize,
        accumulator: usize,
        item: usize,
        body: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaIntegerRangeIndex {
    Int32(AlphaBitvectorKey, AlphaBitvectorKey),
    Integer(usize, usize),
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
    let mut environment = AlphaBindings {
        integer: bindings.clone(),
        bitvector: BTreeMap::new(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        snapshot_aware: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    };
    let mut next_binder = environment
        .integer
        .values()
        .chain(environment.bitvector.values())
        .copied()
        .max()
        .map_or(0, |ordinal| ordinal.saturating_add(1));
    alpha_integer_key_with_bindings(term, &mut environment, &mut next_binder)
}

/// Compare two Integer terms modulo the binders introduced by range folds.
///
/// This is deliberately a checked, memory-free comparison.  Free variables
/// retain their carrier and numeric identity, while Integer and machine item
/// binders are kept in separate alpha environments.  A caller that needs to
/// reason about a term outside this supported fragment receives `None` and
/// can continue through its ordinary proof path.
pub(crate) fn integer_terms_alpha_equivalent(
    left: &SharedIntegerTerm,
    right: &SharedIntegerTerm,
) -> Option<bool> {
    if matches!(left.as_ref(), IntegerTerm::RangeFold { .. })
        || matches!(right.as_ref(), IntegerTerm::RangeFold { .. })
    {
        let left_key = integer_fold_alpha_key(left)?;
        let right_key = integer_fold_alpha_key(right)?;
        return left_key.checked_eq(&right_key);
    }
    let left_key = alpha_integer_key(left.as_ref(), &mut BTreeMap::new())?;
    let right_key = alpha_integer_key(right.as_ref(), &mut BTreeMap::new())?;
    Some(left_key == right_key)
}

/// Build the exact snapshot-aware alpha identity used by fold comparisons.
/// Only a root `IntegerTerm::RangeFold` is admitted; callers needing a larger
/// expression retain the ordinary proof path instead of treating a partial
/// key as authority.
pub(crate) fn integer_fold_alpha_key(term: &SharedIntegerTerm) -> Option<IntegerFoldAlphaKey> {
    if !matches!(term.as_ref(), IntegerTerm::RangeFold { .. }) {
        return None;
    }
    let mut environment = AlphaBindings {
        integer: BTreeMap::new(),
        bitvector: BTreeMap::new(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        snapshot_aware: true,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    };
    let mut next_binder = 0;
    alpha_integer_key_with_bindings(term.as_ref(), &mut environment, &mut next_binder).map(|key| {
        IntegerFoldAlphaKey {
            key,
            work_units: environment.work_units,
        }
    })
}

struct AlphaBindings {
    integer: BTreeMap<Variable, usize>,
    bitvector: BTreeMap<Variable, usize>,
    integer_scope: u64,
    bitvector_scope: u64,
    next_scope_id: u64,
    snapshot_aware: bool,
    registered_load_stack: BTreeSet<Variable>,
    registered_load_memo: HashMap<(Variable, u64, u64, usize), (AlphaRegisteredLoadId, usize)>,
    load_interner: Option<Arc<std::sync::Mutex<AlphaRegisteredLoadInterner>>>,
    work_units: usize,
}

fn alpha_work_checkpoint(bindings: &mut AlphaBindings, units: usize) -> Option<()> {
    bindings.work_units = bindings.work_units.saturating_add(units);
    let exhausted = if bindings.snapshot_aware {
        crate::instrumentation::deadline_exceeded_with_work(units)
    } else {
        crate::instrumentation::record_deterministic_work(units);
        false
    };
    (!exhausted).then_some(())
}

fn alpha_integer_key_with_bindings(
    term: &IntegerTerm,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaIntegerKey> {
    let mut nodes = Vec::new();
    let mut memo = HashMap::new();
    let root = alpha_integer_node(
        &term.clone().into(),
        bindings,
        &mut memo,
        &mut nodes,
        next_binder,
    )?;
    Some(AlphaIntegerKey { nodes, root })
}

fn alpha_integer_node(
    shared: &crate::kernel::SharedIntegerTerm,
    bindings: &mut AlphaBindings,
    memo: &mut HashMap<(u64, u64, u64), usize>,
    nodes: &mut Vec<AlphaIntegerNode>,
    next_binder: &mut usize,
) -> Option<usize> {
    let cache_key = (
        shared.id(),
        bindings.integer_scope,
        bindings.bitvector_scope,
    );
    if let Some(index) = memo.get(&cache_key) {
        return Some(*index);
    }
    let term = shared.as_ref();
    alpha_work_checkpoint(bindings, 1)?;
    let node = match term {
        IntegerTerm::Constant(value) => {
            alpha_work_checkpoint(bindings, (value.bits() as usize).saturating_add(1))?;
            AlphaIntegerNode::Constant(value.clone())
        }
        IntegerTerm::Variable(variable) => {
            AlphaIntegerNode::Variable(alpha_variable_key::<false>(*variable, &bindings.integer)?)
        }
        IntegerTerm::Machine(value) => AlphaIntegerNode::Machine(
            value.ty(),
            alpha_bitvector_key_with_bindings::<false>(value.value(), bindings, next_binder)?,
        ),
        IntegerTerm::Negate(value) => AlphaIntegerNode::Negate(alpha_integer_node(
            value,
            bindings,
            memo,
            nodes,
            next_binder,
        )?),
        IntegerTerm::Add(left, right) => AlphaIntegerNode::Binary {
            operator: IntegerTermBinaryOp::Add,
            left: alpha_integer_node(left, bindings, memo, nodes, next_binder)?,
            right: alpha_integer_node(right, bindings, memo, nodes, next_binder)?,
        },
        IntegerTerm::Subtract(left, right) => AlphaIntegerNode::Binary {
            operator: IntegerTermBinaryOp::Subtract,
            left: alpha_integer_node(left, bindings, memo, nodes, next_binder)?,
            right: alpha_integer_node(right, bindings, memo, nodes, next_binder)?,
        },
        IntegerTerm::Multiply(left, right) => AlphaIntegerNode::Binary {
            operator: IntegerTermBinaryOp::Multiply,
            left: alpha_integer_node(left, bindings, memo, nodes, next_binder)?,
            right: alpha_integer_node(right, bindings, memo, nodes, next_binder)?,
        },
        IntegerTerm::PureFunctionApplication(_) => return None,
        IntegerTerm::AlgebraicMatch { .. } => return None,
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            let alpha_index = match index {
                crate::kernel::IntegerRangeFoldIndex::Int32 { start, end } => {
                    AlphaIntegerRangeIndex::Int32(
                        alpha_bitvector_key_with_bindings::<false>(
                            start.value(),
                            bindings,
                            next_binder,
                        )?,
                        alpha_bitvector_key_with_bindings::<false>(
                            end.value(),
                            bindings,
                            next_binder,
                        )?,
                    )
                }
                crate::kernel::IntegerRangeFoldIndex::Integer { start, end } => {
                    AlphaIntegerRangeIndex::Integer(
                        alpha_integer_node(start, bindings, memo, nodes, next_binder)?,
                        alpha_integer_node(end, bindings, memo, nodes, next_binder)?,
                    )
                }
            };
            let initial = alpha_integer_node(initial, bindings, memo, nodes, next_binder)?;
            let accumulator_index = *next_binder;
            *next_binder = (*next_binder).checked_add(1)?;
            let item_index = *next_binder;
            *next_binder = (*next_binder).checked_add(1)?;
            let old_accumulator = bindings.integer.insert(*accumulator, accumulator_index);
            let item_is_integer =
                matches!(index, crate::kernel::IntegerRangeFoldIndex::Integer { .. });
            let old_item = if matches!(index, crate::kernel::IntegerRangeFoldIndex::Integer { .. })
            {
                bindings.integer.insert(*item, item_index)
            } else {
                bindings.bitvector.insert(*item, item_index)
            };
            let parent_integer_scope = bindings.integer_scope;
            let parent_bitvector_scope = bindings.bitvector_scope;
            let integer_scope = bindings.next_scope_id;
            let mut next_scope_id = integer_scope.checked_add(1)?;
            let bitvector_scope = if item_is_integer {
                parent_bitvector_scope
            } else {
                let scope = next_scope_id;
                next_scope_id = next_scope_id.checked_add(1)?;
                scope
            };
            bindings.next_scope_id = next_scope_id;
            bindings.integer_scope = integer_scope;
            bindings.bitvector_scope = bitvector_scope;
            let body_index = alpha_integer_node(body, bindings, memo, nodes, next_binder);
            bindings.integer_scope = parent_integer_scope;
            bindings.bitvector_scope = parent_bitvector_scope;
            // Restore in reverse insertion order, including an outer binding
            // shadowed by this body. Endpoints and initial stay in outer scope.
            if let Some(previous) = old_item {
                if item_is_integer {
                    bindings.integer.insert(*item, previous);
                } else {
                    bindings.bitvector.insert(*item, previous);
                }
            } else if item_is_integer {
                bindings.integer.remove(item);
            } else {
                bindings.bitvector.remove(item);
            }
            if let Some(previous) = old_accumulator {
                bindings.integer.insert(*accumulator, previous);
            } else {
                bindings.integer.remove(accumulator);
            }
            let body_index = body_index?;
            AlphaIntegerNode::RangeFold {
                index: alpha_index,
                initial,
                accumulator: accumulator_index,
                item: item_index,
                body: body_index,
            }
        }
    };
    let index = nodes.len();
    nodes.push(node);
    memo.insert(cache_key, index);
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

fn alpha_variable_key_with_bindings<const ALLOW_LOADS: bool>(
    variable: Variable,
    bindings: &AlphaBindings,
    carrier_bindings: &BTreeMap<Variable, usize>,
) -> Option<AlphaVariableKey> {
    if let Some(ordinal) = carrier_bindings.get(&variable) {
        return Some(AlphaVariableKey::Bound(*ordinal));
    }
    if bindings.snapshot_aware && crate::kernel::is_load_variable(&variable) {
        // An unbound registered load is represented by its snapshot-bearing
        // load node at bitvector/pointer-offset positions.  Pointer blocks
        // and logical variables have no load form, so reject them here and
        // let the ordinary checked path decide the fact.
        return None;
    }
    alpha_variable_key::<ALLOW_LOADS>(variable, carrier_bindings)
}

fn alpha_registered_load_pointer_with_bindings<const ALLOW_LOADS: bool>(
    variable: Variable,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaRegisteredLoadId> {
    let cache_key = (
        variable,
        bindings.integer_scope,
        bindings.bitvector_scope,
        *next_binder,
    );
    if let Some((load_id, next_after)) = bindings.registered_load_memo.get(&cache_key) {
        *next_binder = *next_after;
        return Some(load_id.clone());
    }
    if !bindings.registered_load_stack.insert(variable) {
        return None;
    }
    let result = (|| {
        let (memory, pointer) = crate::kernel::registered_load_for_variable(&variable)?;
        let snapshot = AlphaSnapshotKey::new(&memory);
        let pointer =
            alpha_pointer_key_with_bindings::<ALLOW_LOADS>(&pointer, bindings, next_binder)?;
        let interner = match bindings.load_interner.clone() {
            Some(interner) => interner,
            None => {
                let interner = alpha_registered_load_interner()?;
                bindings.load_interner = Some(interner.clone());
                interner
            }
        };
        alpha_work_checkpoint(bindings, 1)?;
        let load_id = intern_alpha_registered_load(&interner, snapshot, pointer)?;
        Some((load_id, *next_binder))
    })();
    bindings.registered_load_stack.remove(&variable);
    let (load_id, next_after) = result?;
    bindings
        .registered_load_memo
        .insert(cache_key, (load_id.clone(), next_after));
    Some(load_id)
}

fn alpha_pointer_offset_key_with_bindings<const ALLOW_LOADS: bool>(
    offset: &PointerOffsetTerm,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaPointerOffsetKey> {
    alpha_work_checkpoint(bindings, 1)?;
    Some(match offset {
        PointerOffsetTerm::Constant(value) => AlphaPointerOffsetKey::Constant(*value),
        PointerOffsetTerm::Variable(variable)
            if bindings.snapshot_aware
                && crate::kernel::is_load_variable(variable)
                && !bindings.bitvector.contains_key(variable) =>
        {
            let load_id = alpha_registered_load_pointer_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                next_binder,
            )?;
            AlphaPointerOffsetKey::RegisteredLoad(load_id)
        }
        PointerOffsetTerm::Variable(variable) => {
            AlphaPointerOffsetKey::Variable(alpha_variable_key_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                &bindings.bitvector,
            )?)
        }
        PointerOffsetTerm::Add(left, right) => AlphaPointerOffsetKey::Add(
            Box::new(alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(
                left,
                bindings,
                next_binder,
            )?),
            Box::new(alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(
                right,
                bindings,
                next_binder,
            )?),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            AlphaPointerOffsetKey::Int32Scaled {
                value: Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
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
            value: Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                value,
                bindings,
                next_binder,
            )?),
            byte_width: *byte_width,
            unsigned: *unsigned,
        },
    })
}

fn alpha_pointer_key_with_bindings<const ALLOW_LOADS: bool>(
    pointer: &Pointer,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaPointerKey> {
    alpha_work_checkpoint(bindings, 1)?;
    let block = match &pointer.block {
        PointerBlock::Concrete(name) => AlphaPointerBlockKey::Concrete(name.clone()),
        PointerBlock::StringLiteral { identity, bytes } => AlphaPointerBlockKey::StringLiteral {
            identity: identity.clone(),
            bytes: bytes.clone(),
        },
        PointerBlock::Function(name) => AlphaPointerBlockKey::Function(name.clone()),
        PointerBlock::FunctionSymbolic(variable) => {
            AlphaPointerBlockKey::FunctionSymbolic(alpha_variable_key_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                &bindings.bitvector,
            )?)
        }
        PointerBlock::ExternalArgument => AlphaPointerBlockKey::ExternalArgument,
        PointerBlock::Symbolic(variable) => {
            AlphaPointerBlockKey::Symbolic(alpha_variable_key_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                &bindings.bitvector,
            )?)
        }
        PointerBlock::Heap(identity) => AlphaPointerBlockKey::Heap(*identity),
    };
    Some(AlphaPointerKey {
        block,
        offset: alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(
            &pointer.offset,
            bindings,
            next_binder,
        )?,
    })
}

fn alpha_bitvector_key_with_bindings<const ALLOW_LOADS: bool>(
    term: &Bitvector32Term,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    alpha_work_checkpoint(bindings, 1)?;
    // Load variables hide snapshots too: their binders cannot be treated as
    // opaque free variables by the memory-free structural authority.
    if !ALLOW_LOADS
        && !bindings.snapshot_aware
        && (matches!(term, Bitvector32Term::MemoryLoad(..))
            || matches!(term, Bitvector32Term::Variable(variable) if crate::kernel::is_load_variable(variable)))
    {
        return None;
    }
    let mut binary =
        |operator, left: &Bitvector32Term, right: &Bitvector32Term| -> Option<AlphaBitvectorKey> {
            Some(AlphaBitvectorKey::Binary(
                operator,
                Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                    left,
                    bindings,
                    next_binder,
                )?),
                Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
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
            if let Some(ordinal) = bindings.bitvector.get(variable) {
                AlphaBitvectorKey::Variable(AlphaVariableKey::Bound(*ordinal))
            } else {
                match crate::kernel::is_load_variable(variable)
                    .then(|| crate::kernel::registered_load_for_variable(variable))
                    .flatten()
                {
                    Some(_) if bindings.snapshot_aware => {
                        let load_id = alpha_registered_load_pointer_with_bindings::<ALLOW_LOADS>(
                            *variable,
                            bindings,
                            next_binder,
                        )?;
                        AlphaBitvectorKey::RegisteredLoad(load_id)
                    }
                    Some((_, pointer)) => {
                        AlphaBitvectorKey::Load(Box::new(alpha_pointer_key_with_bindings::<
                            ALLOW_LOADS,
                        >(
                            &pointer, bindings, next_binder
                        )?))
                    }
                    None => AlphaBitvectorKey::Variable(alpha_variable_key_with_bindings::<
                        ALLOW_LOADS,
                    >(
                        *variable,
                        bindings,
                        &bindings.bitvector,
                    )?),
                }
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
            alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder)?,
        )),
        Bitvector32Term::Int64BitwiseNot(body) => {
            AlphaBitvectorKey::Int64BitwiseNot(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(body, bindings, next_binder)?))
        }
        Bitvector32Term::UInt64BitwiseNot(body) => {
            AlphaBitvectorKey::UInt64BitwiseNot(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(
                body, bindings, next_binder
            )?))
        }
        Bitvector32Term::Float32Negate(body) => {
            AlphaBitvectorKey::Float32Negate(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(body, bindings, next_binder)?))
        }
        Bitvector32Term::Float64Negate(body) => {
            AlphaBitvectorKey::Float64Negate(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(body, bindings, next_binder)?))
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => AlphaBitvectorKey::If {
            condition: Box::new(alpha_condition_key_with_bindings::<ALLOW_LOADS>(
                condition,
                bindings,
                next_binder,
            )?),
            then_term: Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                then_term,
                bindings,
                next_binder,
            )?),
            else_term: Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
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
            let start = Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                start,
                bindings,
                next_binder,
            )?);
            let end = Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                end,
                bindings,
                next_binder,
            )?);
            let initial = Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                initial,
                bindings,
                next_binder,
            )?);

            // Range-fold accumulator and item variables are binders just like
            // proposition quantifiers. Canonicalize their body under fresh
            // structural ordinals, then restore any enclosing binding so a
            // fold cannot change the meaning of a sibling term.
            let accumulator_ordinal = *next_binder;
            *next_binder = (*next_binder).checked_add(1)?;
            let previous_accumulator = bindings.bitvector.insert(*accumulator, accumulator_ordinal);
            let item_ordinal = *next_binder;
            *next_binder = (*next_binder).checked_add(1)?;
            let previous_item = bindings.bitvector.insert(*item, item_ordinal);
            let previous_bitvector_scope = bindings.bitvector_scope;
            let bitvector_scope = bindings.next_scope_id;
            bindings.next_scope_id = bindings.next_scope_id.checked_add(1)?;
            bindings.bitvector_scope = bitvector_scope;
            let body =
                alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder);
            bindings.bitvector_scope = previous_bitvector_scope;
            if let Some(previous) = previous_item {
                bindings.bitvector.insert(*item, previous);
            } else {
                bindings.bitvector.remove(item);
            }
            if let Some(previous) = previous_accumulator {
                bindings.bitvector.insert(*accumulator, previous);
            } else {
                bindings.bitvector.remove(accumulator);
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
                        alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                            argument,
                            bindings,
                            next_binder,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?,
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => return None,
        Bitvector32Term::MemoryLoad(memory, pointer) if bindings.snapshot_aware => {
            let snapshot = AlphaSnapshotKey::new(memory);
            let pointer =
                alpha_pointer_key_with_bindings::<ALLOW_LOADS>(pointer, bindings, next_binder)?;
            let interner = match bindings.load_interner.clone() {
                Some(interner) => interner,
                None => {
                    let interner = alpha_registered_load_interner()?;
                    bindings.load_interner = Some(interner.clone());
                    interner
                }
            };
            alpha_work_checkpoint(bindings, 1)?;
            AlphaBitvectorKey::RegisteredLoad(intern_alpha_registered_load(
                &interner, snapshot, pointer,
            )?)
        }
        Bitvector32Term::MemoryLoad(_, pointer) => AlphaBitvectorKey::Load(Box::new(
            alpha_pointer_key_with_bindings::<ALLOW_LOADS>(pointer, bindings, next_binder)?,
        )),
        Bitvector32Term::PointerAddress(pointer) => AlphaBitvectorKey::Address(Box::new(
            alpha_pointer_key_with_bindings::<ALLOW_LOADS>(pointer, bindings, next_binder)?,
        )),
        Bitvector32Term::IntegerToMachine { value, destination } => {
            AlphaBitvectorKey::IntegerToMachine(
                *destination,
                alpha_integer_key_with_bindings(value.as_ref(), bindings, next_binder)?,
            )
        }
        Bitvector32Term::Int64From32(value) => {
            AlphaBitvectorKey::Int64From32(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(value, bindings, next_binder)?))
        }
        Bitvector32Term::UInt64From32(value) => {
            AlphaBitvectorKey::UInt64From32(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(value, bindings, next_binder)?))
        }
        Bitvector32Term::UInt32From64(value) => {
            AlphaBitvectorKey::UInt32From64(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(value, bindings, next_binder)?))
        }
        Bitvector32Term::Int64FromUInt32(value) => {
            AlphaBitvectorKey::Int64FromUInt32(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(
                value, bindings, next_binder
            )?))
        }
        Bitvector32Term::UInt64FromInt32(value) => {
            AlphaBitvectorKey::UInt64FromInt32(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(
                value, bindings, next_binder
            )?))
        }
        Bitvector32Term::UInt64FromInt64(value) => {
            AlphaBitvectorKey::UInt64FromInt64(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(
                value, bindings, next_binder
            )?))
        }
    })
}

// The typed visitor is the production API.  Keep this narrow compatibility
// shim for the legacy unit tests that exercise the old one-map helper directly;
// both carrier maps start from the test's bindings, while the visitor itself
// still applies carrier-aware scope handling.
#[cfg(test)]
fn alpha_bitvector_key<const ALLOW_LOADS: bool>(
    term: &Bitvector32Term,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    let mut typed = AlphaBindings {
        integer: bindings.clone(),
        bitvector: bindings.clone(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        snapshot_aware: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    };
    let result = alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(term, &mut typed, next_binder);
    *bindings = typed.bitvector;
    result
}

fn alpha_condition_key_with_bindings<const ALLOW_LOADS: bool>(
    condition: &ConditionTerm,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaConditionKey> {
    alpha_work_checkpoint(bindings, 1)?;
    let mut binary =
        |operator, left: &Bitvector32Term, right: &Bitvector32Term| -> Option<AlphaConditionKey> {
            Some(AlphaConditionKey::Binary(
                operator,
                alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(left, bindings, next_binder)?,
                alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(right, bindings, next_binder)?,
            ))
        };
    Some(match condition {
        ConditionTerm::Constant(value) => AlphaConditionKey::Constant(*value),
        ConditionTerm::Variable(variable) => {
            AlphaConditionKey::Variable(alpha_variable_key_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                &bindings.bitvector,
            )?)
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
            alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(left, bindings, next_binder)?,
            alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(right, bindings, next_binder)?,
        ),
        ConditionTerm::PointerEqual(left, right) => AlphaConditionKey::PointerEqual(
            alpha_pointer_key_with_bindings::<ALLOW_LOADS>(left, bindings, next_binder)?,
            alpha_pointer_key_with_bindings::<ALLOW_LOADS>(right, bindings, next_binder)?,
        ),
        ConditionTerm::IntegerLessThan(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::LessThan,
            alpha_integer_key_with_bindings(left, bindings, next_binder)?,
            alpha_integer_key_with_bindings(right, bindings, next_binder)?,
        ),
        ConditionTerm::IntegerLessEqual(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::LessEqual,
            alpha_integer_key_with_bindings(left, bindings, next_binder)?,
            alpha_integer_key_with_bindings(right, bindings, next_binder)?,
        ),
        ConditionTerm::IntegerGreaterThan(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::GreaterThan,
            alpha_integer_key_with_bindings(left, bindings, next_binder)?,
            alpha_integer_key_with_bindings(right, bindings, next_binder)?,
        ),
        ConditionTerm::IntegerGreaterEqual(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::GreaterEqual,
            alpha_integer_key_with_bindings(left, bindings, next_binder)?,
            alpha_integer_key_with_bindings(right, bindings, next_binder)?,
        ),
        ConditionTerm::IntegerEqual(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::Equal,
            alpha_integer_key_with_bindings(left, bindings, next_binder)?,
            alpha_integer_key_with_bindings(right, bindings, next_binder)?,
        ),
        ConditionTerm::IntegerNotEqual(left, right) => AlphaConditionKey::IntegerComparison(
            IntegerComparisonOperator::NotEqual,
            alpha_integer_key_with_bindings(left, bindings, next_binder)?,
            alpha_integer_key_with_bindings(right, bindings, next_binder)?,
        ),
        _ => return None,
    })
}

fn alpha_proposition_key<const ALLOW_LOADS: bool>(
    proposition: &Proposition,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaPropositionKey> {
    let mut environment = AlphaBindings {
        integer: BTreeMap::new(),
        bitvector: bindings.clone(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        snapshot_aware: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    };
    alpha_proposition_key_with_bindings::<ALLOW_LOADS>(proposition, &mut environment, next_binder)
}

/// Exact alpha identity for fold equalities whose C payload contains loads.
/// Retained snapshot handles make each load part of the key while the
/// pointer visitor canonicalizes fold-bound C variables by ordinal.
fn snapshot_alpha_proposition_key(
    proposition: &Proposition,
) -> Option<(AlphaPropositionKey, usize)> {
    let mut environment = AlphaBindings {
        integer: BTreeMap::new(),
        bitvector: BTreeMap::new(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        snapshot_aware: true,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    };
    let key = alpha_proposition_key_with_bindings::<true>(proposition, &mut environment, &mut 0)?;
    Some((key, environment.work_units))
}

fn alpha_proposition_key_with_bindings<const ALLOW_LOADS: bool>(
    proposition: &Proposition,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaPropositionKey> {
    alpha_work_checkpoint(bindings, 1)?;
    #[cfg(test)]
    ALPHA_PROPOSITION_KEY_VISITS.with(|visits| visits.set(visits.get() + 1));

    let binary = |left: &Proposition,
                  right: &Proposition,
                  bindings: &mut AlphaBindings,
                  next_binder: &mut usize|
     -> Option<(Box<AlphaPropositionKey>, Box<AlphaPropositionKey>)> {
        let left = Box::new(alpha_proposition_key_with_bindings::<ALLOW_LOADS>(
            left,
            bindings,
            next_binder,
        )?);
        let right = Box::new(alpha_proposition_key_with_bindings::<ALLOW_LOADS>(
            right,
            bindings,
            next_binder,
        )?);
        Some((left, right))
    };
    Some(match proposition {
        Proposition::ConditionIs(condition, value) => AlphaPropositionKey::Condition(
            alpha_condition_key_with_bindings::<ALLOW_LOADS>(condition, bindings, next_binder)?,
            *value,
        ),
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => {
            if !ALLOW_LOADS {
                return None;
            }
            // Loadability is an explicit checked premise, so its memory
            // snapshot is part of the alpha identity.  Raw MemoryLoad terms
            // keep the existing snapshot-blind selection behavior above;
            // only this atom temporarily enables the exact registered-load
            // representation for its selected pointer and width.
            let prior_snapshot_aware = bindings.snapshot_aware;
            bindings.snapshot_aware = true;
            let key = (|| -> Option<AlphaPropositionKey> {
                alpha_work_checkpoint(bindings, 1)?;
                let snapshot = crate::kernel::intern_c_memory_ref(memory);
                Some(AlphaPropositionKey::CMemoryLoadable {
                    memory: AlphaSnapshotKey::new(&snapshot),
                    base: alpha_pointer_key_with_bindings::<ALLOW_LOADS>(
                        base,
                        bindings,
                        next_binder,
                    )?,
                    bytes: alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                        bytes,
                        bindings,
                        next_binder,
                    )?,
                })
            })();
            bindings.snapshot_aware = prior_snapshot_aware;
            key?
        }
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
        Proposition::Not(body) => AlphaPropositionKey::Not(Box::new(
            alpha_proposition_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder)?,
        )),
        Proposition::ForAll { var, sort, body } => {
            let ordinal = *next_binder;
            *next_binder = (*next_binder).checked_add(1)?;
            let body = if *sort == Sort::Integer {
                let prior = bindings.integer.insert(*var, ordinal);
                let parent_scope = bindings.integer_scope;
                let integer_scope = bindings.next_scope_id;
                bindings.next_scope_id = bindings.next_scope_id.checked_add(1)?;
                bindings.integer_scope = integer_scope;
                let body =
                    alpha_proposition_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder);
                bindings.integer_scope = parent_scope;
                if let Some(prior) = prior {
                    bindings.integer.insert(*var, prior);
                } else {
                    bindings.integer.remove(var);
                }
                body
            } else {
                let prior = bindings.bitvector.insert(*var, ordinal);
                let parent_scope = bindings.bitvector_scope;
                let bitvector_scope = bindings.next_scope_id;
                bindings.next_scope_id = bindings.next_scope_id.checked_add(1)?;
                bindings.bitvector_scope = bitvector_scope;
                let body =
                    alpha_proposition_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder);
                bindings.bitvector_scope = parent_scope;
                if let Some(prior) = prior {
                    bindings.bitvector.insert(*var, prior);
                } else {
                    bindings.bitvector.remove(var);
                }
                body
            };
            AlphaPropositionKey::ForAll(sort.clone(), Box::new(body?))
        }
        Proposition::Exists {
            var, sort, body, ..
        } => {
            let ordinal = *next_binder;
            *next_binder = (*next_binder).checked_add(1)?;
            let body = if *sort == Sort::Integer {
                let prior = bindings.integer.insert(*var, ordinal);
                let parent_scope = bindings.integer_scope;
                let integer_scope = bindings.next_scope_id;
                bindings.next_scope_id = bindings.next_scope_id.checked_add(1)?;
                bindings.integer_scope = integer_scope;
                let body =
                    alpha_proposition_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder);
                bindings.integer_scope = parent_scope;
                if let Some(prior) = prior {
                    bindings.integer.insert(*var, prior);
                } else {
                    bindings.integer.remove(var);
                }
                body
            } else {
                let prior = bindings.bitvector.insert(*var, ordinal);
                let parent_scope = bindings.bitvector_scope;
                let bitvector_scope = bindings.next_scope_id;
                bindings.next_scope_id = bindings.next_scope_id.checked_add(1)?;
                bindings.bitvector_scope = bitvector_scope;
                let body =
                    alpha_proposition_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder);
                bindings.bitvector_scope = parent_scope;
                if let Some(prior) = prior {
                    bindings.bitvector.insert(*var, prior);
                } else {
                    bindings.bitvector.remove(var);
                }
                body
            };
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

/// Compare only quantified propositions containing a loadability atom using
/// the checked, snapshot-aware alpha representation. `None` means neither
/// proposition needs this path; `Some(false)` is a fail-closed mismatch,
/// including unsupported or exhausted key construction.
pub(crate) fn snapshot_quantified_alpha_equivalent(
    left: &Proposition,
    right: &Proposition,
) -> Option<bool> {
    let left_has = checked_proposition_contains_memory_loadability(left);
    let right_has = checked_proposition_contains_memory_loadability(right);
    match (left_has, right_has) {
        (Ok(false), Ok(false)) => return None,
        (Ok(false), Ok(true)) | (Ok(true), Ok(false)) | (Err(()), _) | (_, Err(())) => {
            return Some(false);
        }
        (Ok(true), Ok(true)) => {}
    }
    let same_quantifier = match (left, right) {
        (Proposition::ForAll { .. }, Proposition::ForAll { .. }) => true,
        (
            Proposition::Exists {
                name: left_name, ..
            },
            Proposition::Exists {
                name: right_name, ..
            },
        ) => left_name == right_name,
        _ => false,
    };
    if !same_quantifier {
        return Some(false);
    }
    let Some((left_key, left_work)) = snapshot_alpha_proposition_key(left) else {
        return Some(false);
    };
    let Some((right_key, right_work)) = snapshot_alpha_proposition_key(right) else {
        return Some(false);
    };
    if crate::instrumentation::deadline_exceeded_with_work(left_work.saturating_add(right_work)) {
        return Some(false);
    }
    Some(left_key == right_key)
}

fn checked_proposition_contains_memory_loadability(proposition: &Proposition) -> Result<bool, ()> {
    if crate::instrumentation::deadline_exceeded_with_work(1) {
        return Err(());
    }
    match proposition {
        Proposition::CMemoryLoadable { .. } => Ok(true),
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            Ok(checked_proposition_contains_memory_loadability(left)?
                || checked_proposition_contains_memory_loadability(right)?)
        }
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => checked_proposition_contains_memory_loadability(body),
        _ => Ok(false),
    }
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
    use crate::kernel::{SharedIntegerRangeEndpoint, SharedIntegerTerm, SharedMachineIntegerTerm};
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

    #[test]
    fn alpha_integer_to_machine_keys_rename_math_binders_and_include_destination() {
        let make = |variable, destination| Bitvector32Term::IntegerToMachine {
            value: SharedIntegerTerm::from(IntegerTerm::Variable(variable)),
            destination,
        };
        let left = make(Variable(881), MachineIntegerType::Int32);
        let right = make(Variable(882), MachineIntegerType::Int32);
        let renamed_left =
            alpha_bitvector_key::<false>(&left, &mut BTreeMap::from([(Variable(881), 0)]), &mut 1);
        let renamed_right =
            alpha_bitvector_key::<false>(&right, &mut BTreeMap::from([(Variable(882), 0)]), &mut 1);
        assert_eq!(renamed_left, renamed_right);
        assert_ne!(
            renamed_left,
            alpha_bitvector_key::<false>(
                &make(Variable(882), MachineIntegerType::UInt32),
                &mut BTreeMap::from([(Variable(882), 0)]),
                &mut 1,
            )
        );
    }
    fn integer_key_test_fold(
        accumulator: Variable,
        initial: IntegerTerm,
        body: IntegerTerm,
    ) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(2).into(),
            },
            initial,
            accumulator,
            Variable(919),
            body,
        )
    }

    #[test]
    fn integer_fold_alpha_key_distinguishes_free_and_bound_shared_nodes() {
        let x = Variable(917);
        let y = Variable(918);
        let bound = integer_key_test_fold(x, IntegerTerm::var(x), IntegerTerm::var(x));
        let free = integer_key_test_fold(y, IntegerTerm::var(x), IntegerTerm::var(x));
        let renamed = integer_key_test_fold(y, IntegerTerm::var(x), IntegerTerm::var(y));
        let key = |term| alpha_integer_key(term, &mut BTreeMap::new()).unwrap();
        assert_ne!(
            key(&bound),
            key(&free),
            "body occurrence changes meaning at binder"
        );
        assert_eq!(
            key(&bound),
            key(&renamed),
            "renaming a binder preserves meaning"
        );
    }

    #[test]
    fn integer_fold_alpha_key_restores_shadowed_outer_bindings() {
        let x = Variable(917);
        let mut bindings = BTreeMap::from([(x, 0), (Variable(919), 1)]);
        let original = bindings.clone();
        let fold = integer_key_test_fold(x, IntegerTerm::var(x), IntegerTerm::var(x));
        alpha_integer_key(&fold, &mut bindings).unwrap();
        assert_eq!(bindings, original);
    }

    #[test]
    fn integer_fold_alpha_key_keeps_machine_and_integer_binders_distinct() {
        let accumulator = Variable(50_001);
        let item = Variable(50_002);
        let index = crate::kernel::IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
            end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(1)),
        };
        let body = |variable| {
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::IntegerToMachine {
                    value: SharedIntegerTerm::from(IntegerTerm::var(variable)),
                    destination: MachineIntegerType::Int32,
                },
            ))
        };
        let captures_accumulator = IntegerTerm::range_fold(
            index.clone(),
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body(accumulator),
        );
        let captures_free_integer = IntegerTerm::range_fold(
            index,
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body(item),
        );
        let key = |term| alpha_integer_key(term, &mut BTreeMap::new()).unwrap();
        assert_ne!(
            key(&captures_accumulator),
            key(&captures_free_integer),
            "an Int32 item binder must not bind an Integer variable with the same id"
        );
    }

    #[test]
    fn integer_fold_alpha_key_visits_shared_bodies_once_per_scope() {
        let mut work = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut term = IntegerTerm::var(Variable(920));
            for _ in 0..depth {
                let child: SharedIntegerTerm = term.into();
                term = integer_key_test_fold(
                    Variable(921),
                    IntegerTerm::constant_i64(0),
                    IntegerTerm::Add(child.clone(), child),
                );
            }
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                alpha_integer_key(&term, &mut BTreeMap::new()).unwrap()
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(pair[1] <= pair[0] * 3, "{work:?}");
        }
    }
}

#[cfg(test)]
mod snapshot_alpha_tests {
    use super::*;
    use crate::kernel::{
        CMemory, CValue, IntegerRangeFoldIndex, SharedIntegerRangeEndpoint, SharedIntegerTerm,
        SharedMachineIntegerTerm,
    };

    fn int32_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
            end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(2)),
        }
    }

    fn fold_body(memory: &SharedCMemory, item: Variable) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "snapshot-alpha".into(),
                    offset: PointerOffsetTerm::Variable(item),
                }),
            ),
        ))
    }

    fn fold(memory: &SharedCMemory, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            fold_body(memory, item),
        )
    }

    fn registered_load_interner_stats() -> (usize, usize) {
        ALPHA_REGISTERED_LOAD_INTERNER.with(|cell| {
            let Some(interner) = cell.borrow().upgrade() else {
                return (0, 0);
            };
            let Ok(interner) = interner.lock() else {
                return (0, 0);
            };
            let entries = interner.buckets.values().map(Vec::len).sum();
            let live = interner
                .buckets
                .values()
                .flat_map(|bucket| bucket.iter())
                .filter(|candidate| candidate.strong_count() != 0)
                .count();
            (entries, live)
        })
    }

    fn registered_load_interner_live_snapshots() -> BTreeSet<(u32, u32)> {
        ALPHA_REGISTERED_LOAD_INTERNER.with(|cell| {
            let Some(interner) = cell.borrow().upgrade() else {
                return BTreeSet::new();
            };
            let Ok(interner) = interner.lock() else {
                return BTreeSet::new();
            };
            interner
                .buckets
                .values()
                .flat_map(|bucket| bucket.iter())
                .filter_map(|candidate| candidate.upgrade())
                .map(|record| record.snapshot.identity)
                .collect()
        })
    }

    fn equality(term: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(IntegerTerm::constant_i64(9).into(), term.into()),
            true,
        )
    }

    #[test]
    fn snapshot_alpha_fold_loads_require_exact_snapshot_identity() {
        let pointer = Pointer {
            block: "snapshot-alpha".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha", 8));
        let after = crate::kernel::intern_c_memory(
            before
                .as_ref()
                .clone()
                .store(pointer, CValue::Int32(Bitvector32Term::Constant(7))),
        );

        let source = integer_equality_alpha_key(&equality(fold(
            &before,
            Variable(310_000),
            Variable(310_001),
        )))
        .expect("explicit load fold should have an exact alpha key");
        let renamed = integer_equality_alpha_key(&equality(fold(
            &before,
            Variable(311_000),
            Variable(311_001),
        )))
        .expect("renamed explicit load fold should have an exact alpha key");
        let changed_snapshot = integer_equality_alpha_key(&equality(fold(
            &after,
            Variable(311_000),
            Variable(311_001),
        )))
        .expect("changed-snapshot fold should still have a key");

        assert_eq!(source, renamed);
        assert_ne!(source, changed_snapshot);
    }

    #[test]
    fn snapshot_alpha_rejects_unknown_registered_loads() {
        let unknown_load = Variable((1 << 40) + 313);
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha", 8));
        let term = IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            Variable(312_000),
            Variable(312_001),
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::MemoryLoad(
                    memory,
                    Box::new(Pointer {
                        block: "snapshot-alpha".into(),
                        offset: PointerOffsetTerm::Variable(unknown_load),
                    }),
                ),
            )),
        );

        assert!(integer_equality_alpha_key(&equality(term)).is_none());
    }

    #[test]
    fn snapshot_alpha_registered_loads_keep_their_snapshot_identity() {
        let pointer = Pointer {
            block: "snapshot-alpha".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha", 8));
        let after = crate::kernel::intern_c_memory(before.as_ref().clone().store(
            pointer.clone(),
            CValue::Int32(Bitvector32Term::Constant(11)),
        ));
        let before_load =
            crate::kernel::load_variable_for_cell_with_origin(&before, &pointer, &before);
        let after_load =
            crate::kernel::load_variable_for_cell_with_origin(&after, &pointer, &after);

        let make = |load: Variable, accumulator: Variable, item: Variable| {
            IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(load),
                )),
            )
        };
        let before_key = integer_equality_alpha_key(&equality(make(
            before_load,
            Variable(313_000),
            Variable(313_001),
        )))
        .expect("registered load should resolve to an exact key");
        let renamed_before_key = integer_equality_alpha_key(&equality(make(
            before_load,
            Variable(314_000),
            Variable(314_001),
        )))
        .expect("renamed registered load should resolve to an exact key");
        let after_key = integer_equality_alpha_key(&equality(make(
            after_load,
            Variable(314_000),
            Variable(314_001),
        )))
        .expect("registered load from another snapshot should resolve to an exact key");

        assert_eq!(before_key, renamed_before_key);
        assert_ne!(before_key, after_key);
    }

    #[test]
    fn snapshot_alpha_explicit_and_registered_loads_share_nested_identity() {
        let block = "snapshot-alpha-equivalent-loads";
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(block, 64));
        let first_pointer = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let first_load =
            crate::kernel::load_variable_for_cell_with_origin(&memory, &first_pointer, &memory);
        let nested_pointer = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Variable(first_load),
        };
        let nested_load =
            crate::kernel::load_variable_for_cell_with_origin(&memory, &nested_pointer, &memory);
        // The load registry keeps the provenance-projected snapshot used by
        // the minted variable.  Use those exact identities for the explicit
        // forms below; the original `memory` may project to a different DAG
        // epoch even though it names the same source cell.
        let (first_memory, first_registered_pointer) =
            crate::kernel::registered_load_for_variable(&first_load)
                .expect("first load should have a registry entry");
        let (nested_memory, nested_registered_pointer) =
            crate::kernel::registered_load_for_variable(&nested_load)
                .expect("nested load should have a registry entry");
        let fold_with_body = |body: Bitvector32Term| {
            IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(313_100),
                Variable(313_101),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    body,
                )),
            )
        };
        let explicit_first: SharedIntegerTerm = fold_with_body(Bitvector32Term::MemoryLoad(
            first_memory,
            Box::new(first_registered_pointer),
        ))
        .into();
        let registered_first: SharedIntegerTerm =
            fold_with_body(Bitvector32Term::Variable(first_load)).into();
        let explicit_nested: SharedIntegerTerm = fold_with_body(Bitvector32Term::MemoryLoad(
            nested_memory,
            Box::new(nested_registered_pointer),
        ))
        .into();
        let registered_nested: SharedIntegerTerm =
            fold_with_body(Bitvector32Term::Variable(nested_load)).into();

        assert_eq!(
            integer_fold_alpha_key(&explicit_first),
            integer_fold_alpha_key(&registered_first)
        );
        assert_eq!(
            integer_fold_alpha_key(&explicit_nested),
            integer_fold_alpha_key(&registered_nested)
        );
        assert_eq!(
            integer_equality_alpha_key(&equality(explicit_nested.as_ref().clone())),
            integer_equality_alpha_key(&equality(registered_nested.as_ref().clone()))
        );
    }

    #[test]
    fn snapshot_alpha_accepts_free_c_endpoints_and_body_values() {
        let start = Variable(319_000);
        let end = Variable(319_001);
        let payload = Variable(319_002);
        let make = |accumulator: Variable, item: Variable| {
            IntegerTerm::range_fold(
                IntegerRangeFoldIndex::Int32 {
                    start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Variable(start)),
                    end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Variable(end)),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(payload),
                )),
            )
        };
        let source: SharedIntegerTerm = make(Variable(319_010), Variable(319_011)).into();
        let renamed: SharedIntegerTerm = make(Variable(319_020), Variable(319_021)).into();

        assert!(integer_equality_alpha_key(&equality(source.as_ref().clone())).is_some());
        assert_eq!(
            integer_fold_alpha_key(&source),
            integer_fold_alpha_key(&renamed)
        );
        assert_eq!(
            integer_terms_alpha_equivalent(&source, &renamed),
            Some(true)
        );
    }

    #[test]
    fn snapshot_alpha_fold_comparison_uses_exact_snapshot_identity() {
        let pointer = Pointer {
            block: "snapshot-alpha".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha", 8));
        let after = crate::kernel::intern_c_memory(
            before
                .as_ref()
                .clone()
                .store(pointer, CValue::Int32(Bitvector32Term::Constant(13))),
        );
        let make = |memory: &SharedCMemory, accumulator: Variable, item: Variable| {
            let term = fold_body(memory, item);
            IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                term,
            )
        };
        let before_term: SharedIntegerTerm =
            make(&before, Variable(320_000), Variable(320_001)).into();
        let renamed_term: SharedIntegerTerm =
            make(&before, Variable(320_100), Variable(320_101)).into();
        let after_term: SharedIntegerTerm =
            make(&after, Variable(320_100), Variable(320_101)).into();

        assert_eq!(
            integer_terms_alpha_equivalent(&before_term, &renamed_term),
            Some(true)
        );
        assert_eq!(
            integer_terms_alpha_equivalent(&before_term, &after_term),
            Some(false)
        );
    }

    #[test]
    fn snapshot_alpha_nested_folds_canonicalize_load_pointers() {
        let pointer = Pointer {
            block: "snapshot-alpha".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha", 8));
        let after = crate::kernel::intern_c_memory(
            before
                .as_ref()
                .clone()
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(5))),
        );
        let nested = |memory: &SharedCMemory, accumulator: Variable, item: Variable| {
            let inner = fold(memory, Variable(316_000), Variable(316_001));
            IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                inner,
            )
        };
        let source = integer_equality_alpha_key(&equality(nested(
            &before,
            Variable(316_100),
            Variable(316_101),
        )))
        .expect("nested explicit load fold should have an exact alpha key");
        let renamed = integer_equality_alpha_key(&equality(nested(
            &before,
            Variable(317_100),
            Variable(317_101),
        )))
        .expect("renamed nested explicit load fold should have an exact alpha key");
        let changed_snapshot = integer_equality_alpha_key(&equality(nested(
            &after,
            Variable(317_100),
            Variable(317_101),
        )))
        .expect("changed nested snapshot should still have a key");

        assert_eq!(source, renamed);
        assert_ne!(source, changed_snapshot);
    }

    #[test]
    fn snapshot_alpha_work_ignores_unrelated_heap_size() {
        let make_memory = |unrelated_size| {
            crate::kernel::intern_c_memory(
                CMemory::new()
                    .with_block("snapshot-alpha", 8)
                    .with_block("unrelated-snapshot-alpha", unrelated_size),
            )
        };
        let mut work = Vec::new();
        for unrelated_size in [8, 128, 1024, 8192] {
            let memory = make_memory(unrelated_size);
            let term = fold_body(&memory, Variable(318_001));
            let term = IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(318_000),
                Variable(318_001),
                term,
            );
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                integer_equality_alpha_key(&equality(term)).expect("snapshot alpha key")
            });
            work.push(measured);
        }
        let first = work[0];
        for measured in work.into_iter().skip(1) {
            assert!(
                measured <= first + 8,
                "unrelated heap work: {measured} vs {first}"
            );
        }
    }

    fn registered_load_chain(depth: usize) -> (SharedCMemory, Variable) {
        let block = format!("snapshot-alpha-registry-{depth}");
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(block.clone(), 4096));
        let mut pointer = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut load =
            crate::kernel::load_variable_for_cell_with_origin(&memory, &pointer, &memory);
        for _ in 0..depth {
            pointer = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Variable(load),
            };
            load = crate::kernel::load_variable_for_cell_with_origin(&memory, &pointer, &memory);
        }
        (memory, load)
    }

    fn registered_load_branching_chain(depth: usize) -> (SharedCMemory, Variable) {
        let block = format!("snapshot-alpha-registry-branch-{depth}");
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block(block.clone(), 4096));
        let mut pointer = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut load =
            crate::kernel::load_variable_for_cell_with_origin(&memory, &pointer, &memory);
        for _ in 0..depth {
            pointer = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Add(
                    Box::new(PointerOffsetTerm::Variable(load)),
                    Box::new(PointerOffsetTerm::Variable(load)),
                ),
            };
            load = crate::kernel::load_variable_for_cell_with_origin(&memory, &pointer, &memory);
        }
        (memory, load)
    }

    #[test]
    fn snapshot_alpha_registered_load_dags_scale_linearly() {
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let (_memory, load) = registered_load_chain(depth);
            let term = IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(321_000),
                Variable(321_001),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(load),
                )),
            );
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                integer_equality_alpha_key(&equality(term)).expect("registered load DAG key")
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3 + 32,
                "registered load work: {work:?}"
            );
        }
    }

    #[test]
    fn snapshot_alpha_registered_load_branching_dags_stay_linear() {
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let (_memory, load) = registered_load_branching_chain(depth);
            let term = IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(323_000),
                Variable(323_001),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(load),
                )),
            );
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                integer_equality_alpha_key(&equality(term)).expect("branching load DAG key")
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3 + 32,
                "branching registered load work: {work:?}"
            );
        }
    }

    #[test]
    fn snapshot_alpha_registered_load_dags_stop_at_the_active_budget() {
        let (_, load) = registered_load_chain(128);
        let term = IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            Variable(322_000),
            Variable(322_001),
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(load),
            )),
        );
        let tactic = crate::instrumentation::TacticEvent {
            claim: "integer.snapshot_alpha_budget".into(),
            tactic_index: 0,
            tactic_name: "snapshot_alpha_budget".into(),
            class: "simple".into(),
            statement_index: 0,
            source_index: 0,
        };
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 16,
            smart: 16,
            control: 16,
        };
        let ((key, work), events) = crate::instrumentation::with_tactic_work_limits(limits, || {
            crate::instrumentation::collect(|| {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                );
                let result = crate::instrumentation::measure_deterministic_work(|| {
                    integer_equality_alpha_key(&equality(term))
                });
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticFailed(tactic.clone()),
                );
                result
            })
        });
        assert!(key.is_none(), "budgeted snapshot traversal must reject");
        assert!(
            work <= 32,
            "registry traversal exceeded bounded work: {work}"
        );
        assert!(events.iter().any(|event| matches!(
            event,
            crate::instrumentation::VerificationEvent::TacticWorkBudgetExceeded { .. }
        )));
    }

    #[test]
    fn snapshot_alpha_drops_unreachable_registered_load_snapshots() {
        let early_memory =
            crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha-early", 8));
        let early_term: SharedIntegerTerm =
            fold(&early_memory, Variable(324_000), Variable(324_001)).into();
        let early_key = integer_fold_alpha_key(&early_term).expect("early fold key");
        let early_identity = early_memory.arena_id();

        for index in 0..64u64 {
            let block = format!("snapshot-alpha-temporary-{index}");
            let memory =
                crate::kernel::intern_c_memory(CMemory::new().with_block(block.clone(), 8));
            let term: SharedIntegerTerm = IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(324_100 + index * 2),
                Variable(324_101 + index * 2),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::MemoryLoad(
                        memory,
                        Box::new(Pointer {
                            block: block.into(),
                            offset: PointerOffsetTerm::Constant(0),
                        }),
                    ),
                )),
            )
            .into();
            let _temporary_key = integer_fold_alpha_key(&term).expect("temporary fold key");
        }

        let (entries, live) = registered_load_interner_stats();
        assert!(
            entries <= 16,
            "weak registry entries were not cleaned: {entries}"
        );
        assert_eq!(live, 1, "only the retained early load should stay live");
        assert!(registered_load_interner_live_snapshots().contains(&early_identity));
        drop(early_key);

        let mut trigger_key = None;
        for index in 0..16u64 {
            let block = format!("snapshot-alpha-cleanup-trigger-{index}");
            let memory =
                crate::kernel::intern_c_memory(CMemory::new().with_block(block.clone(), 8));
            let term: SharedIntegerTerm = IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(325_000 + index * 2),
                Variable(325_001 + index * 2),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::MemoryLoad(
                        memory,
                        Box::new(Pointer {
                            block: block.into(),
                            offset: PointerOffsetTerm::Constant(0),
                        }),
                    ),
                )),
            )
            .into();
            trigger_key = Some(integer_fold_alpha_key(&term).expect("cleanup trigger key"));
        }
        assert!(!registered_load_interner_live_snapshots().contains(&early_identity));
        drop(trigger_key);
        assert_eq!(registered_load_interner_stats(), (0, 0));
    }

    #[test]
    fn snapshot_alpha_nested_shared_load_dags_scale_linearly() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha", 8));
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let item = Variable(315_001);
            let mut body = fold_body(&memory, item);
            for _ in 0..depth {
                let child: SharedIntegerTerm = body.into();
                body = IntegerTerm::Add(child.clone(), child);
            }
            let term = IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(315_000),
                item,
                body,
            );
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                integer_equality_alpha_key(&equality(term)).expect("shared load DAG key")
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(pair[1] <= pair[0] * 3 + 32, "snapshot alpha work: {work:?}");
        }
    }
}
