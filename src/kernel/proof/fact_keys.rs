//! Structural index keys for persistent checked proof facts.
//!
//! Snapshot-blind keys select a small set of potentially transportable facts.
//! A key match is never proof authority: the checked snapshot bridge still
//! validates every selected candidate.

use crate::kernel::Sort;
use crate::kernel::{
    Bitvector32Term, CMemoryRange, CResource, ConditionTerm, Pointer, PointerBlock,
    PointerOffsetTerm, Proposition, Variable,
};
use std::collections::BTreeMap;

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
    PointerOffsetEqual(SnapshotBlindPointerOffsetKey, SnapshotBlindPointerOffsetKey),
    PointerEqual(SnapshotBlindPointerKey, SnapshotBlindPointerKey),
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

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AlphaVariableKey {
    Bound(usize),
    Free(Variable),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
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
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AlphaBitvectorKey {
    Constant(u32),
    Int64Constant(i64),
    UInt64Constant(u64),
    Variable(AlphaVariableKey),
    Binary(AlphaBitvectorBinaryOp, Box<Self>, Box<Self>),
    BitwiseNot(Box<Self>),
    Int64BitwiseNot(Box<Self>),
    UInt64BitwiseNot(Box<Self>),
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
    Int64From32(Box<Self>),
    UInt64From32(Box<Self>),
    Int64FromUInt32(Box<Self>),
    UInt64FromInt32(Box<Self>),
    UInt64FromInt64(Box<Self>),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
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

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AlphaPointerBlockKey {
    Concrete(String),
    Function(String),
    FunctionSymbolic(AlphaVariableKey),
    ExternalArgument,
    Symbolic(AlphaVariableKey),
    Heap(u64),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct AlphaPointerKey {
    block: AlphaPointerBlockKey,
    offset: AlphaPointerOffsetKey,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
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

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AlphaConditionKey {
    Constant(bool),
    Variable(AlphaVariableKey),
    Binary(AlphaConditionBinaryOp, AlphaBitvectorKey, AlphaBitvectorKey),
    PointerOffsetEqual(AlphaPointerOffsetKey, AlphaPointerOffsetKey),
    PointerEqual(AlphaPointerKey, AlphaPointerKey),
}

fn alpha_variable_key(
    variable: Variable,
    bindings: &BTreeMap<Variable, usize>,
) -> AlphaVariableKey {
    bindings
        .get(&variable)
        .copied()
        .map(AlphaVariableKey::Bound)
        .unwrap_or(AlphaVariableKey::Free(variable))
}

fn alpha_pointer_offset_key(
    offset: &PointerOffsetTerm,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaPointerOffsetKey> {
    Some(match offset {
        PointerOffsetTerm::Constant(value) => AlphaPointerOffsetKey::Constant(*value),
        PointerOffsetTerm::Variable(variable) => {
            AlphaPointerOffsetKey::Variable(alpha_variable_key(*variable, bindings))
        }
        PointerOffsetTerm::Add(left, right) => AlphaPointerOffsetKey::Add(
            Box::new(alpha_pointer_offset_key(left, bindings, next_binder)?),
            Box::new(alpha_pointer_offset_key(right, bindings, next_binder)?),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            AlphaPointerOffsetKey::Int32Scaled {
                value: Box::new(alpha_bitvector_key(value, bindings, next_binder)?),
                byte_width: *byte_width,
            }
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => AlphaPointerOffsetKey::Int64Scaled {
            value: Box::new(alpha_bitvector_key(value, bindings, next_binder)?),
            byte_width: *byte_width,
            unsigned: *unsigned,
        },
    })
}

fn alpha_pointer_key(
    pointer: &Pointer,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaPointerKey> {
    let block = match &pointer.block {
        PointerBlock::Concrete(name) => AlphaPointerBlockKey::Concrete(name.clone()),
        PointerBlock::Function(name) => AlphaPointerBlockKey::Function(name.clone()),
        PointerBlock::FunctionSymbolic(variable) => {
            AlphaPointerBlockKey::FunctionSymbolic(alpha_variable_key(*variable, bindings))
        }
        PointerBlock::ExternalArgument => AlphaPointerBlockKey::ExternalArgument,
        PointerBlock::Symbolic(variable) => {
            AlphaPointerBlockKey::Symbolic(alpha_variable_key(*variable, bindings))
        }
        PointerBlock::Heap(identity) => AlphaPointerBlockKey::Heap(*identity),
    };
    Some(AlphaPointerKey {
        block,
        offset: alpha_pointer_offset_key(&pointer.offset, bindings, next_binder)?,
    })
}

fn alpha_bitvector_key(
    term: &Bitvector32Term,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    let mut binary =
        |operator, left: &Bitvector32Term, right: &Bitvector32Term| -> Option<AlphaBitvectorKey> {
            Some(AlphaBitvectorKey::Binary(
                operator,
                Box::new(alpha_bitvector_key(left, bindings, next_binder)?),
                Box::new(alpha_bitvector_key(right, bindings, next_binder)?),
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
                Some((_, pointer)) => AlphaBitvectorKey::Load(Box::new(alpha_pointer_key(
                    &pointer,
                    bindings,
                    next_binder,
                )?)),
                None => AlphaBitvectorKey::Variable(alpha_variable_key(*variable, bindings)),
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
        Bitvector32Term::BitwiseNot(body) => AlphaBitvectorKey::BitwiseNot(Box::new(
            alpha_bitvector_key(body, bindings, next_binder)?,
        )),
        Bitvector32Term::Int64BitwiseNot(body) => AlphaBitvectorKey::Int64BitwiseNot(Box::new(
            alpha_bitvector_key(body, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt64BitwiseNot(body) => AlphaBitvectorKey::UInt64BitwiseNot(Box::new(
            alpha_bitvector_key(body, bindings, next_binder)?,
        )),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => AlphaBitvectorKey::If {
            condition: Box::new(alpha_condition_key(condition, bindings, next_binder)?),
            then_term: Box::new(alpha_bitvector_key(then_term, bindings, next_binder)?),
            else_term: Box::new(alpha_bitvector_key(else_term, bindings, next_binder)?),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let start = Box::new(alpha_bitvector_key(start, bindings, next_binder)?);
            let end = Box::new(alpha_bitvector_key(end, bindings, next_binder)?);
            let initial = Box::new(alpha_bitvector_key(initial, bindings, next_binder)?);

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
            let body = alpha_bitvector_key(body, bindings, next_binder);
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
                    .map(|argument| alpha_bitvector_key(argument, bindings, next_binder))
                    .collect::<Option<Vec<_>>>()?,
            }
        }
        Bitvector32Term::MemoryLoad(_, pointer) => {
            AlphaBitvectorKey::Load(Box::new(alpha_pointer_key(pointer, bindings, next_binder)?))
        }
        Bitvector32Term::Int64From32(value) => AlphaBitvectorKey::Int64From32(Box::new(
            alpha_bitvector_key(value, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt64From32(value) => AlphaBitvectorKey::UInt64From32(Box::new(
            alpha_bitvector_key(value, bindings, next_binder)?,
        )),
        Bitvector32Term::Int64FromUInt32(value) => AlphaBitvectorKey::Int64FromUInt32(Box::new(
            alpha_bitvector_key(value, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt64FromInt32(value) => AlphaBitvectorKey::UInt64FromInt32(Box::new(
            alpha_bitvector_key(value, bindings, next_binder)?,
        )),
        Bitvector32Term::UInt64FromInt64(value) => AlphaBitvectorKey::UInt64FromInt64(Box::new(
            alpha_bitvector_key(value, bindings, next_binder)?,
        )),
    })
}

fn alpha_condition_key(
    condition: &ConditionTerm,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaConditionKey> {
    let mut binary =
        |operator, left: &Bitvector32Term, right: &Bitvector32Term| -> Option<AlphaConditionKey> {
            Some(AlphaConditionKey::Binary(
                operator,
                alpha_bitvector_key(left, bindings, next_binder)?,
                alpha_bitvector_key(right, bindings, next_binder)?,
            ))
        };
    Some(match condition {
        ConditionTerm::Constant(value) => AlphaConditionKey::Constant(*value),
        ConditionTerm::Variable(variable) => {
            AlphaConditionKey::Variable(alpha_variable_key(*variable, bindings))
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
            alpha_pointer_offset_key(left, bindings, next_binder)?,
            alpha_pointer_offset_key(right, bindings, next_binder)?,
        ),
        ConditionTerm::PointerEqual(left, right) => AlphaConditionKey::PointerEqual(
            alpha_pointer_key(left, bindings, next_binder)?,
            alpha_pointer_key(right, bindings, next_binder)?,
        ),
        _ => return None,
    })
}

fn alpha_proposition_key(
    proposition: &Proposition,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaPropositionKey> {
    let binary = |left: &Proposition,
                  right: &Proposition,
                  bindings: &mut BTreeMap<Variable, usize>,
                  next_binder: &mut usize|
     -> Option<(Box<AlphaPropositionKey>, Box<AlphaPropositionKey>)> {
        let left = Box::new(alpha_proposition_key(left, bindings, next_binder)?);
        let right = Box::new(alpha_proposition_key(right, bindings, next_binder)?);
        Some((left, right))
    };
    Some(match proposition {
        Proposition::ConditionIs(condition, value) => AlphaPropositionKey::Condition(
            alpha_condition_key(condition, bindings, next_binder)?,
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
        Proposition::Not(body) => AlphaPropositionKey::Not(Box::new(alpha_proposition_key(
            body,
            bindings,
            next_binder,
        )?)),
        Proposition::ForAll { var, sort, body } => {
            let ordinal = *next_binder;
            *next_binder += 1;
            let prior = bindings.insert(*var, ordinal);
            let body = alpha_proposition_key(body, bindings, next_binder);
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
            let body = alpha_proposition_key(body, bindings, next_binder);
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
    alpha_proposition_key(proposition, &mut BTreeMap::new(), &mut 0).map(QuantifiedEquivalenceKey)
}
