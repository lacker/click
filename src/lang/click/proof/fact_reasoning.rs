use super::*;

/// The fixed set of condition forms accepted by
/// `condition_polarity_equivalent`. Callers can probe an exact index for these
/// instead of maintaining another project-sized index.
pub(super) fn condition_polarity_forms(proposition: &Proposition) -> Vec<Proposition> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition.clone(), *value),
        Proposition::Not(negated) => match negated.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition.clone(), !value),
            _ => return Vec::new(),
        },
        _ => return Vec::new(),
    };
    let mut conditions = vec![(condition, value)];
    if let Some((left, right, strict)) =
        canonical_order_condition(&conditions[0].0, conditions[0].1)
    {
        let left = Box::new(left);
        let right = Box::new(right);
        let mut equivalent = if strict {
            vec![
                (
                    ConditionTerm::Bitvector32SignedLessThan(left.clone(), right.clone()),
                    true,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterEqual(left.clone(), right.clone()),
                    false,
                ),
                (
                    ConditionTerm::Bitvector32SignedLessEqual(right.clone(), left.clone()),
                    false,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterThan(right, left),
                    true,
                ),
            ]
        } else {
            vec![
                (
                    ConditionTerm::Bitvector32SignedLessEqual(left.clone(), right.clone()),
                    true,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterThan(left.clone(), right.clone()),
                    false,
                ),
                (
                    ConditionTerm::Bitvector32SignedLessThan(right.clone(), left.clone()),
                    false,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterEqual(right, left),
                    true,
                ),
            ]
        };
        conditions.append(&mut equivalent);
    }
    let mut forms = Vec::new();
    for (condition, value) in conditions {
        let direct = Proposition::ConditionIs(condition.clone(), value);
        if !forms.contains(&direct) {
            forms.push(direct);
        }
        let negated = Proposition::Not(Box::new(Proposition::ConditionIs(condition, !value)));
        if !forms.contains(&negated) {
            forms.push(negated);
        }
    }
    forms
}

/// Structural key that deliberately forgets memory snapshot identities in
/// load atoms. A matching key only selects candidates; the kernel snapshot
/// bridge still proves that a selected candidate denotes the required fact.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::lang::click) enum SnapshotBlindPropositionKey {
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
pub(in crate::lang::click) struct SnapshotBlindMemoryRangeKey {
    block: PointerBlock,
    offset: SnapshotBlindPointerOffsetKey,
    start: SnapshotBlindBitvectorKey,
    end: SnapshotBlindBitvectorKey,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::lang::click) enum SnapshotBlindConditionKey {
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
pub(in crate::lang::click) enum SnapshotBlindBitvectorKey {
    Load(Box<SnapshotBlindPointerKey>),
    Add(Box<Self>, Box<Self>),
    Subtract(Box<Self>, Box<Self>),
    Multiply(Box<Self>, Box<Self>),
    Exact(Bitvector32Term),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::lang::click) struct SnapshotBlindPointerKey {
    block: PointerBlock,
    offset: Box<SnapshotBlindPointerOffsetKey>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::lang::click) enum SnapshotBlindPointerOffsetKey {
    Add(Box<Self>, Box<Self>),
    Int32Scaled {
        value: SnapshotBlindBitvectorKey,
        byte_width: i64,
    },
    Exact(PointerOffsetTerm),
}

/// One-pass alpha-invariant key for the quantified logical/condition
/// fragment used by replay premises. Bound variables are represented by
/// structural ordinals while free variables retain their kernel identities.
/// Memory snapshots in loads are deliberately omitted, matching the
/// separately checked canonical-form replay equivalence.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct QuantifiedReplayKey(AlphaPropositionKey);

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
    Remainder,
    ShiftLeft,
    ArithmeticShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AlphaBitvectorKey {
    Constant(u32),
    Variable(AlphaVariableKey),
    Binary(AlphaBitvectorBinaryOp, Box<Self>, Box<Self>),
    BitwiseNot(Box<Self>),
    If {
        condition: Box<AlphaConditionKey>,
        then_term: Box<Self>,
        else_term: Box<Self>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<Self>,
    },
    Load(Box<AlphaPointerKey>),
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
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AlphaPointerBlockKey {
    Concrete(String),
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

impl SnapshotBlindPropositionKey {
    pub(super) fn forgets_a_snapshot(&self) -> bool {
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
            Self::Int32Scaled { value, .. } => value.forgets_a_snapshot(),
            Self::Exact(_) => false,
        }
    }
}

pub(in crate::lang::click) fn snapshot_blind_proposition_key(
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
        // A load variable keys as the load it represents: one O(1)
        // registry lookup, no snapshot in the key, and canonical forms
        // bucket with the load terms of the same cell.
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
        offset => SnapshotBlindPointerOffsetKey::Exact(offset.clone()),
    }
}

pub(super) fn exact_fact_is_available(required: &Proposition, available: &[Proposition]) -> bool {
    available
        .iter()
        .any(|fact| exact_fact_contains_conjunct(fact, required))
}

/// Structural proposition equality whose condition leaves are decided by the
/// kernel's snapshot bridge: two forms of one compound fact whose load
/// atoms carry different certified snapshots. Structure must match exactly,
/// so this never accepts a weaker or stronger proposition.
fn propositions_equal_modulo_proven_snapshots(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            left_value == right_value
                && assumptions
                    .conditions_equal_modulo_proven_snapshots(left_condition, right_condition)
        }
        (Proposition::Implies(left_a, left_b), Proposition::Implies(right_a, right_b)) => {
            propositions_equal_modulo_proven_snapshots(left_a, right_a, assumptions)
                && propositions_equal_modulo_proven_snapshots(left_b, right_b, assumptions)
        }
        (Proposition::And(left_a, left_b), Proposition::And(right_a, right_b))
        | (Proposition::Or(left_a, left_b), Proposition::Or(right_a, right_b)) => {
            propositions_equal_modulo_proven_snapshots(left_a, right_a, assumptions)
                && propositions_equal_modulo_proven_snapshots(left_b, right_b, assumptions)
        }
        (Proposition::Not(left_body), Proposition::Not(right_body)) => {
            propositions_equal_modulo_proven_snapshots(left_body, right_body, assumptions)
        }
        // Separations compare part-wise; the work lives in a never-inlined
        // helper because this function participates in deep proposition
        // recursion where added frame bytes overflow the stack.
        (
            left @ Proposition::CResourceSeparate { .. },
            right @ Proposition::CResourceSeparate { .. },
        ) => separations_equal_modulo_proven_snapshots(left, right, assumptions),
        _ => false,
    }
}

/// Proves that one already-selected structural candidate is the same fact as
/// `required` across certified memory snapshots. Candidate selection remains
/// the caller's responsibility; this operation never searches a context.
/// Resolves load variables in comparison term positions only:
/// condition terms and pointer offsets, never descending into embedded
/// memory snapshots. The full resolver walks whole snapshots and is far too
/// expensive for per-candidate comparison paths.
fn resolve_canonical_bitvector_shallow(bits: &Bitvector32Term) -> Bitvector32Term {
    match bits {
        Bitvector32Term::Variable(variable) if crate::kernel::is_load_variable(variable) => {
            match crate::kernel::registered_load_for_variable(variable) {
                Some((memory, pointer)) => Bitvector32Term::MemoryLoad(memory, Box::new(pointer)),
                None => bits.clone(),
            }
        }
        Bitvector32Term::Add(left, right) => Bitvector32Term::Add(
            Box::new(resolve_canonical_bitvector_shallow(left)),
            Box::new(resolve_canonical_bitvector_shallow(right)),
        ),
        Bitvector32Term::Subtract(left, right) => Bitvector32Term::Subtract(
            Box::new(resolve_canonical_bitvector_shallow(left)),
            Box::new(resolve_canonical_bitvector_shallow(right)),
        ),
        Bitvector32Term::Multiply(left, right) => Bitvector32Term::Multiply(
            Box::new(resolve_canonical_bitvector_shallow(left)),
            Box::new(resolve_canonical_bitvector_shallow(right)),
        ),
        _ => bits.clone(),
    }
}

fn resolve_canonical_offset_shallow(value: &PointerOffsetTerm) -> PointerOffsetTerm {
    match value {
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::Int32Scaled {
            value: Box::new(resolve_canonical_bitvector_shallow(value)),
            byte_width: *byte_width,
        },
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::Add(
            Box::new(resolve_canonical_offset_shallow(left)),
            Box::new(resolve_canonical_offset_shallow(right)),
        ),
        _ => value.clone(),
    }
}

/// `snapshot_bridged_fact_is_available` where the caller already holds the
/// assumption context the bridge should reason in.
///
/// Candidates still come only from `available`, so widening the assumptions
/// cannot make an unlisted fact available — the wider context only decides
/// whether two forms denote one fact.
/// A separation required at one snapshot is available when an available
/// separation names the same regions modulo the certified frame. Condition
/// facts need no such bridge: terms are canonical at creation, so one fact
/// has one form.
pub(super) fn separation_bridged_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
    framing: &[ExecutionPureFact],
) -> bool {
    matches!(required, Proposition::CResourceSeparate { .. })
        && separation_bridged_available(required, available, assumptions, framing)
}

pub(super) fn exact_fact_contains_conjunct(fact: &Proposition, required: &Proposition) -> bool {
    condition_polarity_equivalent(fact, required)
        || matches!(fact, Proposition::And(left, right)
            if exact_fact_contains_conjunct(left, required)
                || exact_fact_contains_conjunct(right, required))
}

/// True only when `required` is a proper conjunct of an available conjunction.
/// This is the exact, structural rule checked by the simple `extract` tactic;
/// it performs no normalization, snapshot transport, or proposition search.
pub(super) fn exact_proper_conjunct_is_available(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    available.iter().any(|fact| {
        matches!(fact, Proposition::And(_, _)) && exact_fact_contains_conjunct(fact, required)
    })
}

/// Modus ponens as a bounded structural rule for the simple `extract` tactic:
/// `required` is a consequent reached by walking an available (possibly
/// chained) implication whose antecedents are each themselves available
/// facts. Antecedents and the consequent match exactly, up to condition
/// polarity, or by the snapshot bridge — never by derivation. Work is linear
/// in the available facts times the implication depth; nothing is searched.
pub(super) fn discharged_implication_consequent_is_available(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    if !available
        .iter()
        .any(|fact| matches!(fact, Proposition::Implies(_, _)))
    {
        return false;
    }
    let assumptions = assumptions_from_propositions(available);
    let fact_available = |needed: &Proposition| {
        pure_fact_is_replay_available(needed, available)
            || available.iter().any(|fact| {
                condition_polarity_equivalent(fact, needed)
                    || propositions_equal_modulo_proven_snapshots(fact, needed, &assumptions)
            })
    };
    available.iter().any(|fact| {
        let mut current = fact;
        while let Proposition::Implies(antecedent, consequent) = current {
            if !fact_available(antecedent) {
                return false;
            }
            if propositions_equal_modulo_proven_snapshots(consequent, required, &assumptions) {
                return true;
            }
            current = consequent;
        }
        false
    })
}

pub(super) fn propositions_are_exact_negations(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => left_condition == right_condition && left_value != right_value,
        (Proposition::Not(body), proposition) | (proposition, Proposition::Not(body)) => {
            body.as_ref() == proposition
                || matches!(
                    (body.as_ref(), proposition),
                    (
                        Proposition::ConditionIs(left_condition, left_value),
                        Proposition::ConditionIs(right_condition, right_value),
                    ) if left_condition == right_condition && left_value == right_value
                )
        }
        _ => false,
    }
}

pub(super) fn negate_click_proposition(proposition: &ClickProposition) -> ClickProposition {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => ClickProposition::Comparison {
            left: left.clone(),
            operator: match operator {
                ComparisonOperator::Equal => ComparisonOperator::NotEqual,
                ComparisonOperator::NotEqual => ComparisonOperator::Equal,
                ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
                ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
                ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
                ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
            },
            right: right.clone(),
        },
        ClickProposition::Not(body) => body.as_ref().clone(),
        proposition => ClickProposition::Not(Box::new(proposition.clone())),
    }
}

pub(in crate::lang::click) fn condition_polarity_equivalent(
    left: &Proposition,
    right: &Proposition,
) -> bool {
    if left == right {
        return true;
    }
    // A negated condition fact is the same total boolean condition with the
    // opposite expected value; flattening lets one form compare against
    // the other and against the canonical order form of either.
    let flatten = |proposition: &Proposition| match proposition {
        Proposition::ConditionIs(condition, value) => Some((condition.clone(), *value)),
        Proposition::Not(negated) => match negated.as_ref() {
            Proposition::ConditionIs(condition, value) => Some((condition.clone(), !value)),
            _ => None,
        },
        _ => None,
    };
    let (Some((left_condition, left_value)), Some((right_condition, right_value))) =
        (flatten(left), flatten(right))
    else {
        return false;
    };
    if left_condition == right_condition && left_value == right_value {
        return true;
    }
    matches!(
        (
            canonical_order_condition(&left_condition, left_value),
            canonical_order_condition(&right_condition, right_value),
        ),
        (Some(left), Some(right)) if left == right
    )
}

fn canonical_order_condition(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        _ => None,
    }
}

pub(super) fn quantified_replay_equivalent_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    let required = required.clone();
    if !matches!(required, Proposition::ForAll { .. }) {
        return None;
    }
    available.iter().find_map(|fact| {
        let fact = fact.clone();
        if !matches!(fact, Proposition::ForAll { .. }) {
            return None;
        }
        let forward = assumptions_from_propositions(std::slice::from_ref(&fact))
            .derive_simp_proposition(&required)
            .is_some();
        let reverse = assumptions_from_propositions(std::slice::from_ref(&required))
            .derive_simp_proposition(&fact)
            .is_some();
        (forward && reverse).then_some(fact)
    })
}

pub(super) fn quantified_binder_equivalent(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort
                && substitute_int32_variable_in_proposition(
                    left_body,
                    *left_var,
                    Bitvector32Term::Variable(*right_var),
                ) == **right_body
        }
        (
            Proposition::Exists {
                name: left_name,
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::Exists {
                name: right_name,
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_name == right_name
                && left_sort == right_sort
                && substitute_int32_variable_in_proposition(
                    left_body,
                    *left_var,
                    Bitvector32Term::Variable(*right_var),
                ) == **right_body
        }
        _ => false,
    }
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
    bindings: &BTreeMap<Variable, usize>,
) -> Option<AlphaPointerOffsetKey> {
    Some(match offset {
        PointerOffsetTerm::Constant(value) => AlphaPointerOffsetKey::Constant(*value),
        PointerOffsetTerm::Variable(variable) => {
            AlphaPointerOffsetKey::Variable(alpha_variable_key(*variable, bindings))
        }
        PointerOffsetTerm::Add(left, right) => AlphaPointerOffsetKey::Add(
            Box::new(alpha_pointer_offset_key(left, bindings)?),
            Box::new(alpha_pointer_offset_key(right, bindings)?),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            AlphaPointerOffsetKey::Int32Scaled {
                value: Box::new(alpha_bitvector_key(value, bindings)?),
                byte_width: *byte_width,
            }
        }
    })
}

fn alpha_pointer_key(
    pointer: &Pointer,
    bindings: &BTreeMap<Variable, usize>,
) -> Option<AlphaPointerKey> {
    let block = match &pointer.block {
        PointerBlock::Concrete(name) => AlphaPointerBlockKey::Concrete(name.clone()),
        PointerBlock::ExternalArgument => AlphaPointerBlockKey::ExternalArgument,
        PointerBlock::Symbolic(variable) => {
            AlphaPointerBlockKey::Symbolic(alpha_variable_key(*variable, bindings))
        }
        PointerBlock::Heap(identity) => AlphaPointerBlockKey::Heap(*identity),
    };
    Some(AlphaPointerKey {
        block,
        offset: alpha_pointer_offset_key(&pointer.offset, bindings)?,
    })
}

fn alpha_bitvector_key(
    term: &Bitvector32Term,
    bindings: &BTreeMap<Variable, usize>,
) -> Option<AlphaBitvectorKey> {
    let binary =
        |operator, left: &Bitvector32Term, right: &Bitvector32Term| -> Option<AlphaBitvectorKey> {
            Some(AlphaBitvectorKey::Binary(
                operator,
                Box::new(alpha_bitvector_key(left, bindings)?),
                Box::new(alpha_bitvector_key(right, bindings)?),
            ))
        };
    Some(match term {
        Bitvector32Term::Constant(value) => AlphaBitvectorKey::Constant(*value),
        // A load variable keys as the load it represents: the load key is
        // snapshot-blind, so a universal recorded with load terms and one
        // lowered to load variables share a bucket. A bound index inside the
        // load variable keys by its binder ordinal rather than by the load
        // variable's id.
        Bitvector32Term::Variable(variable) => {
            match crate::kernel::is_load_variable(variable)
                .then(|| crate::kernel::registered_load_for_variable(variable))
                .flatten()
            {
                Some((_, pointer)) => {
                    AlphaBitvectorKey::Load(Box::new(alpha_pointer_key(&pointer, bindings)?))
                }
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
        Bitvector32Term::Remainder(left, right) => {
            binary(AlphaBitvectorBinaryOp::Remainder, left, right)?
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            binary(AlphaBitvectorBinaryOp::ShiftLeft, left, right)?
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            binary(AlphaBitvectorBinaryOp::ArithmeticShiftRight, left, right)?
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
        Bitvector32Term::BitwiseNot(body) => {
            AlphaBitvectorKey::BitwiseNot(Box::new(alpha_bitvector_key(body, bindings)?))
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => AlphaBitvectorKey::If {
            condition: Box::new(alpha_condition_key(condition, bindings)?),
            then_term: Box::new(alpha_bitvector_key(then_term, bindings)?),
            else_term: Box::new(alpha_bitvector_key(else_term, bindings)?),
        },
        Bitvector32Term::RangeFold { .. } => return None,
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            AlphaBitvectorKey::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| alpha_bitvector_key(argument, bindings))
                    .collect::<Option<Vec<_>>>()?,
            }
        }
        Bitvector32Term::MemoryLoad(_, pointer) => {
            AlphaBitvectorKey::Load(Box::new(alpha_pointer_key(pointer, bindings)?))
        }
    })
}

fn alpha_condition_key(
    condition: &ConditionTerm,
    bindings: &BTreeMap<Variable, usize>,
) -> Option<AlphaConditionKey> {
    let binary =
        |operator, left: &Bitvector32Term, right: &Bitvector32Term| -> Option<AlphaConditionKey> {
            Some(AlphaConditionKey::Binary(
                operator,
                alpha_bitvector_key(left, bindings)?,
                alpha_bitvector_key(right, bindings)?,
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
            alpha_pointer_offset_key(left, bindings)?,
            alpha_pointer_offset_key(right, bindings)?,
        ),
        ConditionTerm::PointerEqual(left, right) => AlphaConditionKey::PointerEqual(
            alpha_pointer_key(left, bindings)?,
            alpha_pointer_key(right, bindings)?,
        ),
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
        Proposition::ConditionIs(condition, value) => {
            AlphaPropositionKey::Condition(alpha_condition_key(condition, bindings)?, *value)
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

/// Returns a linear-time persistent-index key for a universal in the covered
/// logical/condition fragment. Unsupported atomic families return `None` and
/// remain on their legacy replay path rather than being placed in a broad
/// bucket. Selecting a candidate by this key proves nothing; the quantified
/// replay judgment still validates it.
pub(super) fn quantified_replay_index_key(
    proposition: &Proposition,
) -> Option<QuantifiedReplayKey> {
    if !matches!(proposition, Proposition::ForAll { .. }) {
        return None;
    }
    alpha_proposition_key(proposition, &mut BTreeMap::new(), &mut 0).map(QuantifiedReplayKey)
}

/// See the doc comment below: a generation-side recognizer only, comparing
/// bodies up to per-level binder renaming. Terms are canonical at creation,
/// so two lowerings of one fact are structurally equal.
pub(super) fn nested_quantified_binder_equivalent(
    left: &Proposition,
    right: &Proposition,
    depth: usize,
) -> bool {
    nested_quantified_binder_equivalent_exact(left, right, depth)
}

fn nested_quantified_binder_equivalent_exact(
    left: &Proposition,
    right: &Proposition,
    depth: usize,
) -> bool {
    if depth == 0 {
        return false;
    }
    if quantified_binder_equivalent(left, right) {
        return true;
    }
    match (left, right) {
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort
                && nested_quantified_binder_equivalent_exact(
                    &substitute_int32_variable_in_proposition(
                        left_body,
                        *left_var,
                        Bitvector32Term::Variable(*right_var),
                    ),
                    right_body,
                    depth - 1,
                )
        }
        _ => false,
    }
}

pub(super) fn pure_fact_is_replay_available(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    available.contains(required)
        || exactly_available_fact(required, available).is_some()
        || available
            .iter()
            .any(|fact| quantified_binder_equivalent(required, fact))
        || quantified_replay_equivalent_available_fact(required, available).is_some()
}

pub(super) fn atomic_conjuncts<'a>(
    proposition: &'a Proposition,
    output: &mut Vec<&'a Proposition>,
) {
    match proposition {
        Proposition::And(left, right) => {
            atomic_conjuncts(left, output);
            atomic_conjuncts(right, output);
        }
        proposition => output.push(proposition),
    }
}

/// The available fact, or conjunct of one, exactly equal to `required`.
pub(in crate::lang::click) fn exactly_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    fn matching_conjunct(fact: &Proposition, required: &Proposition) -> Option<Proposition> {
        if fact == required {
            return Some(fact.clone());
        }
        let Proposition::And(left, right) = fact else {
            return None;
        };
        matching_conjunct(left, required).or_else(|| matching_conjunct(right, required))
    }

    available
        .iter()
        .find_map(|fact| matching_conjunct(fact, required))
}

pub(super) fn directly_matching_separation_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    let assumptions = assumptions_from_propositions(available);
    directly_matching_separation_fact_under(required, available, &assumptions)
}

/// `directly_matching_separation_fact` where the caller already holds the
/// assumption context the match should reason in (for example the available
/// facts plus recorded execution effect facts, which let the bounded resource
/// matcher see that two load terms from different snapshots denote one
/// pointer). Candidates still come only from `available`, so widening the
/// assumptions cannot make an unlisted fact available.
pub(super) fn directly_matching_separation_fact_under(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
) -> Option<Proposition> {
    let Proposition::CResourceSeparate {
        left: required_left,
        right: required_right,
    } = required
    else {
        return None;
    };
    available.iter().find_map(|fact| {
        let Proposition::CResourceSeparate { left, right } = fact else {
            return None;
        };
        let same_orientation = c_resources_directly_match(left, required_left, assumptions)
            && c_resources_directly_match(right, required_right, assumptions);
        let reverse_orientation = c_resources_directly_match(left, required_right, assumptions)
            && c_resources_directly_match(right, required_left, assumptions);
        (same_orientation || reverse_orientation).then(|| fact.clone())
    })
}

pub(super) fn directly_covering_loadability_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    matches!(required, Proposition::CMemoryLoadable { .. }).then_some(())?;
    available.iter().find_map(|fact| {
        matches!(fact, Proposition::CMemoryLoadable { .. })
            .then(|| {
                assumptions_from_propositions(std::slice::from_ref(fact))
                    .derive_atomic_proposition(required)
                    .map(|_| fact.clone())
            })
            .flatten()
    })
}

pub(super) fn proposition_has_contextual_derivation_rules(proposition: &Proposition) -> bool {
    !matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapAllocationFreed { .. }
    )
}

fn minimize_derivation_premises(
    initial: PropositionDerivation,
    derive: impl Fn(&[Proposition]) -> Option<PropositionDerivation>,
) -> Result<PropositionDerivation, ClickError> {
    fn remove_group(
        selected: Vec<Proposition>,
        candidates: &[Proposition],
        derive: &impl Fn(&[Proposition]) -> Option<PropositionDerivation>,
    ) -> Result<Vec<Proposition>, ClickError> {
        check_verification_deadline()?;
        let candidate_set = candidates.iter().collect::<BTreeSet<_>>();
        let reduced = selected
            .iter()
            .filter(|premise| !candidate_set.contains(premise))
            .cloned()
            .collect::<Vec<_>>();
        if !reduced.is_empty() && derive(&reduced).is_some() {
            return Ok(reduced);
        }
        if candidates.len() <= 1 {
            return Ok(selected);
        }
        let middle = candidates.len() / 2;
        let selected = remove_group(selected, &candidates[..middle], derive)?;
        remove_group(selected, &candidates[middle..], derive)
    }

    let candidates = initial.context_premises();
    let selected = remove_group(candidates.clone(), &candidates, &derive)?;
    check_verification_deadline()?;
    Ok(derive(&selected).unwrap_or(initial))
}

pub(super) fn minimal_proposition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Result<Option<PropositionDerivation>, ClickError> {
    if !proposition_has_contextual_derivation_rules(proposition) {
        return Ok(None);
    }
    if matches!(proposition, Proposition::ConditionIs(_, _)) {
        return search_condition_derivation(proposition, available);
    }
    let derive = |facts: &[Proposition]| {
        let assumptions = assumptions_from_propositions(facts);
        assumptions
            .derive_proposition(proposition)
            .or_else(|| assumptions.derive_simp_proposition(proposition))
    };
    check_verification_deadline()?;
    let Some(initial) = derive(available) else {
        check_verification_deadline()?;
        return Ok(None);
    };
    check_verification_deadline()?;
    Ok(Some(minimize_derivation_premises(initial, derive)?))
}

fn condition_search_budget_error(proposition: &Proposition, candidate_count: usize) -> ClickError {
    ClickError::new(format!(
        "condition-certificate premise search exceeded the active verification budget\n  target: {}\n  ambient condition facts: {candidate_count}\n  context: {}\nprovide the exact premises with simple tactics to continue",
        describe_pure_fact(proposition, &[], &[]),
        crate::instrumentation::deadline_context(),
    ))
}

pub(super) fn describe_condition_search_miss(
    proposition: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let candidate_count = available
        .iter()
        .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
        .count();
    format!(
        "condition-certificate premise search did not derive {} from {candidate_count} ambient condition facts: {}; smart search tries individual facts and pairs and is heuristic, so split the execution into smaller steps or provide the exact premises with simple tactics",
        describe_pure_fact(proposition, parameters, arguments),
        describe_pure_facts(
            &available
                .iter()
                .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
                .cloned()
                .collect::<Vec<_>>()
        ),
    )
}

pub(super) fn describe_derivation_failure(
    proposition: &Proposition,
    available: &[Proposition],
) -> String {
    if matches!(proposition, Proposition::ConditionIs(_, _)) {
        describe_condition_search_miss(proposition, available, &[], &[])
    } else {
        bounded_debug(proposition)
    }
}

fn check_condition_search_budget(
    proposition: &Proposition,
    candidate_count: usize,
) -> Result<(), ClickError> {
    if crate::instrumentation::deadline_exceeded() {
        Err(condition_search_budget_error(proposition, candidate_count))
    } else {
        Ok(())
    }
}

pub(in crate::lang::click) fn search_condition_derivation(
    proposition: &Proposition,
    available: &[Proposition],
) -> Result<Option<PropositionDerivation>, ClickError> {
    let candidates = available
        .iter()
        .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _)))
        .collect::<Vec<_>>();
    check_condition_search_budget(proposition, candidates.len())?;
    let derive = |facts: &[Proposition]| {
        let assumptions = assumptions_from_propositions(facts);
        assumptions
            .derive_atomic_proposition(proposition)
            .or_else(|| assumptions.derive_simp_atomic_proposition(proposition))
    };
    for fact in &candidates {
        check_condition_search_budget(proposition, candidates.len())?;
        if let Some(derivation) = derive(std::slice::from_ref(*fact)) {
            check_condition_search_budget(proposition, candidates.len())?;
            return Ok(Some(derivation));
        }
        check_condition_search_budget(proposition, candidates.len())?;
    }
    // Two-premise derivations keep the former pair enumeration — same
    // ordering, same two-fact contexts — but only over pairs some derivation
    // could connect: two facts sharing a bitvector variable, or two facts
    // each sharing one with the goal. A candidate pair sharing neither is
    // jointly satisfiable whenever each fact is (their variables are
    // disjoint), and a fact unsatisfiable alone was already found by the
    // single-candidate pass, so skipping the pair cannot lose a derivation.
    // The former enumeration reran the prover once per ambient pair, which is
    // quadratic in unrelated conditions.
    let goal_variables = crate::kernel::condition_fact_variables(proposition);
    let candidate_variables = candidates
        .iter()
        .map(|fact| crate::kernel::condition_fact_variables(fact))
        .collect::<Vec<_>>();
    let mut variable_buckets = BTreeMap::<Variable, Vec<usize>>::new();
    let mut goal_connected = Vec::new();
    for (index, variables) in candidate_variables.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        if variables
            .iter()
            .any(|variable| goal_variables.contains(variable))
        {
            goal_connected.push(index);
        }
        for variable in variables {
            variable_buckets.entry(*variable).or_default().push(index);
        }
    }
    let mut candidate_pairs = BTreeSet::new();
    for bucket in variable_buckets.values() {
        for (position, first) in bucket.iter().enumerate() {
            for second in &bucket[position + 1..] {
                crate::instrumentation::record_deterministic_work(1);
                candidate_pairs.insert((*first.min(second), *first.max(second)));
            }
        }
    }
    for (position, first) in goal_connected.iter().enumerate() {
        for second in &goal_connected[position + 1..] {
            crate::instrumentation::record_deterministic_work(1);
            candidate_pairs.insert((*first.min(second), *first.max(second)));
        }
    }
    for (first, second) in candidate_pairs {
        check_condition_search_budget(proposition, candidates.len())?;
        if let Some(derivation) = derive(&[candidates[first].clone(), candidates[second].clone()]) {
            check_condition_search_budget(proposition, candidates.len())?;
            return Ok(Some(derivation));
        }
        check_condition_search_budget(proposition, candidates.len())?;
    }
    // Derivations needing three or more premises come from one derivation
    // over the complete candidate set, minimized to its actual dependencies —
    // the same shape `minimal_proposition_derivation` uses for every other
    // goal. The empty-context guard keeps a context-free tautology from
    // acquiring a derivation here, since this search's contract is premises
    // drawn from the candidate facts.
    if candidates.is_empty() {
        return Ok(None);
    }
    check_condition_search_budget(proposition, candidates.len())?;
    let complete = candidates
        .iter()
        .map(|fact| (*fact).clone())
        .collect::<Vec<_>>();
    let Some(initial) = derive(&complete) else {
        check_condition_search_budget(proposition, candidates.len())?;
        return Ok(None);
    };
    check_condition_search_budget(proposition, candidates.len())?;
    Ok(Some(minimize_derivation_premises(initial, derive)?))
}

pub(super) fn exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    let left = left.clone();
    let right = right.clone();
    normalized_exact_facts_directly_conflict(&left, &right)
}

fn normalized_exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (Proposition::And(first, second), _) => {
            normalized_exact_facts_directly_conflict(first, right)
                || normalized_exact_facts_directly_conflict(second, right)
        }
        (_, Proposition::And(first, second)) => {
            normalized_exact_facts_directly_conflict(left, first)
                || normalized_exact_facts_directly_conflict(left, second)
        }
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => left_condition == right_condition && left_value != right_value,
        (Proposition::Not(body), proposition) | (proposition, Proposition::Not(body)) => {
            body.as_ref() == proposition
        }
        _ => false,
    }
}

pub(super) fn fact_conflicts_with_assumptions(
    fact: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    match fact {
        Proposition::And(left, right) => {
            fact_conflicts_with_assumptions(left, assumptions)
                || fact_conflicts_with_assumptions(right, assumptions)
        }
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => assumptions.proves(body),
        fact => assumptions.proves(&Proposition::Not(Box::new(fact.clone()))),
    }
}

pub(super) fn assumptions_for_direct_fact_transport(
    propositions: &[Proposition],
) -> PureFactContext {
    fn collect(proposition: &Proposition, facts: &mut Vec<Proposition>) {
        match proposition {
            Proposition::ConditionIs(_, _)
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapAllocationFreed { .. }
            | Proposition::CResourceSeparate { .. }
            // Owned ranges in one composition are pairwise separate; the
            // effect-disjointness legs of direct transport need that
            // separation when no explicit separate(...) fact writes it.
            | Proposition::CResourceComposition(_) => facts.push(proposition.clone()),
            Proposition::And(left, right) => {
                collect(left, facts);
                collect(right, facts);
            }
            _ => {}
        }
    }

    let mut facts = Vec::new();
    for proposition in propositions {
        collect(proposition, &mut facts);
    }
    assumptions_from_propositions(&facts)
}

pub(super) fn facts_for_direct_surface_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = Vec::new();
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        facts.extend(
            conjuncts
                .into_iter()
                .filter(|&proposition| is_direct_surface_lowering_fact(proposition))
                .cloned(),
        );
    }
    facts.sort();
    facts.dedup();
    facts
}

pub(super) fn is_direct_surface_lowering_fact(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CResourceSeparate { .. }
            | Proposition::CResourceContains { .. }
            | Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapAllocationFreed { .. }
    )
}

pub(super) fn facts_for_direct_derivation_lowering(
    propositions: &[Proposition],
) -> Vec<Proposition> {
    let mut facts = facts_for_direct_surface_lowering(propositions);
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        for proposition in conjuncts {
            let direct_condition = matches!(
                proposition,
                Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), _)
            ) || matches!(proposition, Proposition::ConditionIs(_, _))
                && !c_condition_fact_has_memory(proposition);
            if direct_condition && !facts.contains(proposition) {
                facts.push(proposition.clone());
            }
        }
    }
    facts
}

/// Facts that may establish that a restricted simplifier's surface goal and
/// premises are defined without performing an equality step on its behalf.
/// Array bounds are part of expression lowering; equalities remain available
/// only through the explicitly listed `simp() using` premises.
pub(super) fn facts_for_restricted_simp_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_direct_surface_lowering(propositions);
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        for proposition in conjuncts {
            if matches!(
                proposition,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(_, _)
                        | ConditionTerm::Bitvector32SignedLessEqual(_, _)
                        | ConditionTerm::Bitvector32SignedGreaterThan(_, _)
                        | ConditionTerm::Bitvector32SignedGreaterEqual(_, _),
                    _,
                )
            ) && !facts.contains(proposition)
            {
                facts.push(proposition.clone());
            }
        }
    }
    facts
}

pub(super) fn facts_for_smart_have_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_direct_derivation_lowering(propositions);
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        for proposition in conjuncts {
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                proposition
            else {
                continue;
            };
            let is_atomic_alias = matches!(
                (left.as_ref(), right.as_ref()),
                (
                    Bitvector32Term::MemoryLoad(_, _),
                    Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_)
                ) | (
                    Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_),
                    Bitvector32Term::MemoryLoad(_, _)
                )
            );
            if is_atomic_alias && !facts.contains(proposition) {
                facts.push(proposition.clone());
            }
        }
    }
    facts
}

pub(super) fn facts_for_simple_goal_lowering(propositions: &[Proposition]) -> Vec<Proposition> {
    let mut facts = facts_for_smart_have_lowering(propositions);
    for proposition in propositions {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(proposition, &mut conjuncts);
        for proposition in conjuncts {
            let include = match proposition {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(_, _)
                    | ConditionTerm::Bitvector32SignedLessEqual(_, _)
                    | ConditionTerm::Bitvector32SignedGreaterThan(_, _)
                    | ConditionTerm::Bitvector32SignedGreaterEqual(_, _)
                    | ConditionTerm::PointerOffsetEqual(_, _),
                    _,
                ) => true,
                // A false-polarity atomic alias decides branch conditions
                // (`if (p[i] == x)`) whose negative arm the goal's `If` terms
                // still carry; the smart-have set only admits the true polarity.
                Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), false) => {
                    matches!(
                        (left.as_ref(), right.as_ref()),
                        (
                            Bitvector32Term::MemoryLoad(_, _),
                            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_)
                        ) | (
                            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_),
                            Bitvector32Term::MemoryLoad(_, _)
                        )
                    )
                }
                _ => false,
            };
            if include && !facts.contains(proposition) {
                facts.push(proposition.clone());
            }
        }
    }
    facts
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        CMemory, CMemoryRange, CResource, CValue, Pointer, PointerBlock, PointerOffsetTerm,
        Variable, intern_c_memory, load_variable_for_cell_with_origin,
    };

    #[test]
    fn canonical_origin_transport_suppresses_general_snapshot_alias_search() {
        let preserved = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let written = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(4),
        };
        let before = CMemory::new();
        let after = before
            .clone()
            .store(written.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
        let assumptions =
            PureFactContext::new().assume_proposition(Proposition::CMemoryMutatesOnly {
                before: before.clone(),
                after: after.clone(),
                pointers: vec![written],
            });
        // The canonical memories are the cells' epochs. Snapshots that
        // differ only by a declared block or a write to another cell share
        // an epoch, so a synthetic marker block would not separate these
        // load variables; a write to the queried cell does (the second pair).
        let left = load_variable_for_cell_with_origin(
            &intern_c_memory(before.clone()),
            &preserved,
            &intern_c_memory(before.clone()),
        );
        let right = load_variable_for_cell_with_origin(
            &intern_c_memory(after.clone()),
            &preserved,
            &intern_c_memory(after.clone()),
        );

        let unchanged = OriginsUnchanged::new(&assumptions).decide(left, right);
        assert!(
            unchanged,
            "the effect fact should transport the preserved cell"
        );

        // Also force the snapshot-comparison fallback with a write to the
        // queried cell. The answer is false, but the load-variable bridge
        // must reach that answer through the bounded alias route rather than
        // re-entering the general alias search it exists to avoid.
        let loaded = preserved;
        let changed_before =
            CMemory::new().store(loaded.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
        let changed_after = changed_before
            .clone()
            .store(loaded.clone(), CValue::Int32(Bitvector32Term::Constant(2)));
        let changed_left = load_variable_for_cell_with_origin(
            &intern_c_memory(changed_before.clone()),
            &loaded,
            &intern_c_memory(changed_before),
        );
        let changed_right = load_variable_for_cell_with_origin(
            &intern_c_memory(changed_after.clone()),
            &loaded,
            &intern_c_memory(changed_after),
        );
        assert_ne!(
            changed_left, changed_right,
            "a write to the cell separates its names"
        );
        let (changed_unchanged, events) = crate::instrumentation::collect(|| {
            OriginsUnchanged::new(&PureFactContext::new()).decide(changed_left, changed_right)
        });
        assert!(
            !changed_unchanged,
            "a write to the loaded cell must not be transported as unchanged"
        );
        assert!(
            events.iter().any(|event| matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "snapshot comparison: bounded alias"
            )),
            "the regression must exercise bounded snapshot comparison: {events:#?}"
        );
        assert!(
            events.iter().all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "snapshot comparison: general alias"
            )),
            "canonical-origin transport must not re-enter general alias search: {events:#?}"
        );
    }

    #[test]
    fn quantified_replay_key_is_alpha_invariant_and_preserves_free_variables() {
        let quantified =
            |outer: Variable, inner: Variable, free: Variable, name: &str| Proposition::ForAll {
                var: outer,
                sort: Sort::CInt32,
                body: Box::new(Proposition::And(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(
                            Box::new(Bitvector32Term::Variable(outer)),
                            Box::new(Bitvector32Term::Variable(free)),
                        ),
                        true,
                    )),
                    Box::new(Proposition::Exists {
                        name: name.to_string(),
                        var: inner,
                        sort: Sort::CInt32,
                        body: Box::new(Proposition::ConditionIs(
                            ConditionTerm::Bitvector32Equal(
                                Box::new(Bitvector32Term::Variable(inner)),
                                Box::new(Bitvector32Term::Variable(outer)),
                            ),
                            true,
                        )),
                    }),
                )),
            };

        let left = quantified(Variable(0), Variable(1), Variable(7), "left name");
        let renamed = quantified(
            Variable(10_000),
            Variable(20_000),
            Variable(7),
            "right name",
        );
        let different_free = quantified(
            Variable(10_000),
            Variable(20_000),
            Variable(8),
            "right name",
        );

        assert_eq!(
            quantified_replay_index_key(&left),
            quantified_replay_index_key(&renamed),
            "binder identities and existential display names are not semantic"
        );
        assert_ne!(
            quantified_replay_index_key(&left),
            quantified_replay_index_key(&different_free),
            "free variable identities remain part of the key"
        );
    }

    #[test]
    fn quantified_replay_key_sees_through_load_variables() {
        // A universal lowered to load variables keys as the loads those
        // variables represent. A bound index inside a load variable keys by
        // binder ordinal, so renamed binders share a bucket with each other
        // and with the same universal written in load terms.
        let memory = intern_c_memory(CMemory::new().with_block("p", 12));
        let cell = |index: Variable| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "p".into(),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: Box::new(Bitvector32Term::Variable(index)),
                        byte_width: 4,
                    },
                }),
            )
        };
        let universal = |index: Variable, term: Bitvector32Term| Proposition::ForAll {
            var: index,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(term),
                    Box::new(Bitvector32Term::Variable(index)),
                ),
                true,
            )),
        };
        let named = |index: Variable| crate::kernel::canonical_term(&cell(index));
        assert!(matches!(
            named(Variable(3_000_000)),
            Bitvector32Term::Variable(_)
        ));
        let left = universal(Variable(3_000_000), named(Variable(3_000_000)));
        let renamed = universal(Variable(2_000_000), named(Variable(2_000_000)));
        let written = universal(Variable(3_000_001), cell(Variable(3_000_001)));
        assert_eq!(
            quantified_replay_index_key(&left),
            quantified_replay_index_key(&renamed)
        );
        assert_eq!(
            quantified_replay_index_key(&left),
            quantified_replay_index_key(&written)
        );
        assert!(quantified_binder_equivalent(&left, &renamed));
    }

    /// The perpetual-service `fold(service(owner))` near-miss: the body's
    /// separation fact is available from the unfold, but the fold point
    /// rewrites it through a memory that retains this path's store cells, so
    /// the two forms print identically yet compare structurally unequal.
    /// The bounded separation matcher must equate them from the recorded
    /// pointer-offset equality and separation facts, without the open-ended
    /// kernel search whose budget truncation used to be misreported as a
    /// missing fact.
    #[test]
    fn fold_body_separation_fact_matches_across_store_snapshots() {
        let owner_base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                byte_width: 4,
            },
        };
        let owner_field = |bytes: i64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(owner_base.offset.clone()),
                Box::new(PointerOffsetTerm::Constant(bytes)),
            ),
        };
        let phase_field = owner_field(4);
        let cell_field = owner_field(8);
        let load = |memory: &CMemory, pointer: &Pointer| {
            Bitvector32Term::MemoryLoad(intern_c_memory(memory.clone()), Box::new(pointer.clone()))
        };
        let empty = CMemory::new();
        // The form recorded when the resource body was unfolded: the cell
        // pointer read through the call-havoc snapshot.
        let havoc = CMemory::new().with_block("havoc:1000000", 0);
        // The form carried by the recorded execution facts: the same
        // loads read through the branch-entry memory with its retained cells.
        let entry = empty
            .clone()
            .store(
                phase_field.clone(),
                CValue::Int32(load(&empty, &phase_field)),
            )
            .store(owner_base.clone(), CValue::Int32(load(&empty, &owner_base)));
        let cell_element_offset = |memory: &CMemory| PointerOffsetTerm::Int32Scaled {
            value: Box::new(load(memory, &cell_field)),
            byte_width: 4,
        };
        // The fold-point form reads the cell pointer through a memory
        // that still carries the `owner->cell[0] = owner->phase` store, whose
        // written address is itself written through a loaded pointer, so no
        // assumption-free normalization can drop the cell.
        let folded = havoc.clone().store(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: cell_element_offset(&havoc),
            },
            CValue::Int32(load(&havoc, &owner_base)),
        );
        let separation = |left_start: u32, left_end: u32, cell_memory: &CMemory| {
            Proposition::CResourceSeparate {
                left: CResource::Memory(CMemoryRange::new(
                    owner_base.clone(),
                    Bitvector32Term::Constant(left_start),
                    Bitvector32Term::Constant(left_end),
                )),
                right: CResource::Memory(CMemoryRange::new(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: cell_element_offset(cell_memory),
                    },
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )),
            }
        };
        let required = separation(0, 4, &folded);
        let available = separation(0, 4, &havoc);

        // The two forms print identically but are different propositions,
        // so plain exact matching must miss.
        assert_ne!(required, available);
        assert_eq!(
            describe_pure_fact(&required, &[], &[]),
            describe_pure_fact(&available, &[], &[]),
        );
        assert!(!exact_fact_is_available(
            &required,
            std::slice::from_ref(&available)
        ));

        // The recorded execution facts: the two forms of the cell pointer
        // denote one offset, and the loaded pointer's field is separate from
        // the written cell range.
        let offsets_equal = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(
                Box::new(cell_element_offset(&havoc)),
                Box::new(cell_element_offset(&entry)),
            ),
            true,
        );
        let fields_separate = separation(2, 4, &entry);
        let assumptions =
            assumptions_from_propositions(&[offsets_equal.clone(), fields_separate.clone()]);
        assert_eq!(
            directly_matching_separation_fact_under(
                &required,
                std::slice::from_ref(&available),
                &assumptions,
            ),
            Some(available.clone()),
            "the bounded separation matcher must transport the unfold form to the fold point"
        );
    }
}

/// One side of an equality that load-variable bridging can walk.
///
/// The bridging argument is identical for pointer-offset and int32
/// equalities — only the shape of a side and of the equality differ — so one
/// implementation serves both.
trait LoadVariableBridgeSide: Clone + PartialEq + Sized {
    /// The load variable this side represents, when it represents one.
    fn load_variable(&self) -> Option<Variable>;
    /// The two sides of an equality of this shape.
    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)>;
    /// An equality of this shape over the two sides.
    fn equality(left: Self, right: Self) -> Proposition;
}

impl LoadVariableBridgeSide for PointerOffsetTerm {
    fn load_variable(&self) -> Option<Variable> {
        let PointerOffsetTerm::Int32Scaled { value, .. } = self else {
            return None;
        };
        value.as_ref().load_variable()
    }

    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)> {
        let Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) =
            proposition
        else {
            return None;
        };
        Some((left.as_ref().clone(), right.as_ref().clone()))
    }

    fn equality(left: Self, right: Self) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(left), Box::new(right)),
            true,
        )
    }
}

impl LoadVariableBridgeSide for Bitvector32Term {
    /// A side represents a load either with its load variable or with the
    /// load term itself; both forms denote one atom, so both answer here.
    fn load_variable(&self) -> Option<Variable> {
        match self {
            Bitvector32Term::Variable(variable) => {
                crate::kernel::is_load_variable(variable).then_some(*variable)
            }
            Bitvector32Term::MemoryLoad(_, _) => {
                crate::kernel::load_variable_for_term(self).map(|(variable, _)| variable)
            }
            _ => None,
        }
    }

    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)> {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            proposition
        else {
            return None;
        };
        Some((left.as_ref().clone(), right.as_ref().clone()))
    }

    fn equality(left: Self, right: Self) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
            true,
        )
    }
}

/// Whether an equality premise follows from recorded equalities of the same
/// shape by chaining through load variables. Load variables are invisible to
/// Click source, so a premise and the recorded facts may legitimately write
/// one user-level equality through different intermediate variables. The
/// closure is bounded: only equality facts with a load-variable endpoint
/// contribute edges, and the walk visits each side at most once.
fn bridged_by_load_variable_edges<S: LoadVariableBridgeSide>(
    premise: &Proposition,
    facts: &[Proposition],
) -> bool {
    let Some((start, goal)) = S::equality_sides(premise) else {
        return false;
    };
    let edges: Vec<(S, S)> = facts
        .iter()
        .filter_map(S::equality_sides)
        .filter(|(left, right)| left.load_variable().is_some() || right.load_variable().is_some())
        .collect();
    if edges.is_empty() {
        return false;
    }
    let mut frontier = vec![start];
    let mut visited: Vec<S> = Vec::new();
    while let Some(current) = frontier.pop() {
        if current == goal {
            return true;
        }
        if visited.contains(&current) {
            continue;
        }
        visited.push(current.clone());
        for (left, right) in &edges {
            if left == &current && !visited.contains(right) {
                frontier.push(right.clone());
            } else if right == &current && !visited.contains(left) {
                frontier.push(left.clone());
            }
        }
    }
    false
}

/// Decides, and remembers, whether two load variables stand for one cell
/// that framing shows unchanged between their origin snapshots.
struct OriginsUnchanged<'a> {
    assumptions: &'a PureFactContext,
    decided: std::collections::HashMap<(Variable, Variable), bool>,
}

impl<'a> OriginsUnchanged<'a> {
    fn new(assumptions: &'a PureFactContext) -> Self {
        Self {
            assumptions,
            decided: std::collections::HashMap::new(),
        }
    }

    fn decide(&mut self, left: Variable, right: Variable) -> bool {
        let key = if left.0 <= right.0 {
            (left, right)
        } else {
            (right, left)
        };
        if let Some(decided) = self.decided.get(&key) {
            return *decided;
        }
        let decided = self.compute(key.0, key.1);
        self.decided.insert(key, decided);
        decided
    }

    fn compute(&self, left: Variable, right: Variable) -> bool {
        let (Some((left_memory, left_pointer)), Some((right_memory, right_pointer))) = (
            crate::kernel::registered_load_origin_for_variable(&left),
            crate::kernel::registered_load_origin_for_variable(&right),
        ) else {
            return false;
        };
        // Bounded: the unchanged proof must come from the cheap routes —
        // recorded derivations crossed with exact-fact distinctness — never
        // from whole-snapshot alias search, which is the giant-term
        // recursion load-variable construction exists to avoid.
        left_pointer == right_pointer
            && crate::kernel::with_isolated_memory_resolution_fuel(8_000, || {
                crate::kernel::with_bounded_snapshot_comparison(|| {
                    crate::kernel::c_memory_load_is_unchanged(
                        &left_memory,
                        &right_memory,
                        &left_pointer,
                        self.assumptions,
                    ) || crate::kernel::c_memory_load_is_unchanged(
                        &right_memory,
                        &left_memory,
                        &left_pointer,
                        self.assumptions,
                    )
                })
            })
    }
}

/// The forms of `side` that represent the same cell as one of `endpoints`.
fn origin_renamings<S: LoadVariableBridgeSide>(
    side: &S,
    endpoints: &[S],
    origins: &mut OriginsUnchanged<'_>,
) -> Vec<S> {
    let Some(variable) = side.load_variable() else {
        return vec![side.clone()];
    };
    let mut forms = vec![side.clone()];
    for endpoint in endpoints {
        let candidate = endpoint.load_variable().expect("filtered by the caller");
        if candidate != variable && origins.decide(variable, candidate) && !forms.contains(endpoint)
        {
            forms.push(endpoint.clone());
        }
    }
    forms
}

fn bridged_with_origins<S: LoadVariableBridgeSide>(
    premise: &Proposition,
    facts: &[Proposition],
    assumptions: &PureFactContext,
) -> bool {
    let Some((start, goal)) = S::equality_sides(premise) else {
        return false;
    };
    let mut origins = OriginsUnchanged::new(assumptions);
    // Two load variables for one unchanged cell need no fact edge at all:
    // when the premise equates them directly, the origins-unchanged proof is
    // the whole content.
    if let (Some(start_variable), Some(goal_variable)) =
        (start.load_variable(), goal.load_variable())
        && origins.decide(start_variable, goal_variable)
    {
        return true;
    }
    // One implicit hop only: rename the premise's canonical endpoints onto
    // fact endpoints naming the same cell, then ask the plain fact-edge
    // closure.
    let endpoints: Vec<S> = facts
        .iter()
        .filter_map(S::equality_sides)
        .flat_map(|(left, right)| [left, right])
        .filter(|side| side.load_variable().is_some())
        .collect();
    let start_forms = origin_renamings(&start, &endpoints, &mut origins);
    let goal_forms = origin_renamings(&goal, &endpoints, &mut origins);
    for start_form in &start_forms {
        for goal_form in &goal_forms {
            if start_form == goal_form {
                return true;
            }
            let candidate = S::equality(start_form.clone(), goal_form.clone());
            if bridged_by_load_variable_edges::<S>(&candidate, facts) {
                return true;
            }
        }
    }
    false
}

pub(in crate::lang::click) fn premise_bridged_by_load_variable_chain(
    premise: &Proposition,
    facts: &[Proposition],
) -> bool {
    match premise {
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true) => {
            bridged_by_load_variable_edges::<PointerOffsetTerm>(premise, facts)
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true) => {
            bridged_by_load_variable_edges::<Bitvector32Term>(premise, facts)
        }
        _ => false,
    }
}

/// The chain closure with origin-unchanged implicit edges. Two load variables
/// additionally connect when the loads they represent are
/// provably unchanged between their origin snapshots under the supplied
/// assumptions (call effect summaries and frame evidence). Reserved for
/// once-per-tactic consumers such as explicit transport and rewrite premise
/// checks — the unchanged proof is assumption-based and must stay off hot
/// fact paths.
pub(in crate::lang::click) fn premise_bridged_by_load_variable_chain_with_origins(
    premise: &Proposition,
    facts: &[Proposition],
    assumptions: &PureFactContext,
) -> bool {
    if premise_bridged_by_load_variable_chain(premise, facts) {
        return true;
    }
    match premise {
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true) => {
            bridged_with_origins::<PointerOffsetTerm>(premise, facts, assumptions)
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true) => {
            bridged_with_origins::<Bitvector32Term>(premise, facts, assumptions)
        }
        _ => false,
    }
}

/// The separation branch of bridged availability. Keep its range and
/// proposition temporaries out of the shared fact-dispatch frame; the
/// expansion small-stack regression pins that boundary.
#[inline(never)]
fn separation_bridged_available(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
    framing: &[ExecutionPureFact],
) -> bool {
    let assumptions = framing
        .iter()
        .fold(assumptions.clone(), |assumptions, fact| {
            assumptions.assume_proposition(fact.proposition().clone())
        });
    available.iter().any(|candidate| {
        matches!(candidate, Proposition::CResourceSeparate { .. })
            && propositions_equal_modulo_proven_snapshots(candidate, required, &assumptions)
    })
}

/// Whether two separations denote the same fact after canonicalization and
/// proven snapshot comparison: each range's base offset and extent terms
/// compare with load variables resolved shallowly and load atoms bridged
/// across proven snapshots — the relation the condition arm uses, applied
/// to the terms a separation is made of. Separation is symmetric, so both pairings are
/// tried. Keep its range temporaries local rather than charging every caller;
/// the expansion small-stack regression pins that boundary.
#[inline(never)]
fn separations_equal_modulo_proven_snapshots(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let (
        Proposition::CResourceSeparate {
            left: CResource::Memory(left_a),
            right: CResource::Memory(left_b),
        },
        Proposition::CResourceSeparate {
            left: CResource::Memory(right_a),
            right: CResource::Memory(right_b),
        },
    ) = (left, right)
    else {
        return false;
    };
    let ranges_equal = |left: &CMemoryRange, right: &CMemoryRange| {
        left.base().block == right.base().block
            && assumptions.conditions_equal_modulo_proven_snapshots(
                &ConditionTerm::PointerOffsetEqual(
                    Box::new(resolve_canonical_offset_shallow(&left.base().offset)),
                    Box::new(PointerOffsetTerm::Constant(0)),
                ),
                &ConditionTerm::PointerOffsetEqual(
                    Box::new(resolve_canonical_offset_shallow(&right.base().offset)),
                    Box::new(PointerOffsetTerm::Constant(0)),
                ),
            )
            && assumptions.conditions_equal_modulo_proven_snapshots(
                &ConditionTerm::Bitvector32Equal(
                    Box::new(resolve_canonical_bitvector_shallow(left.start())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                &ConditionTerm::Bitvector32Equal(
                    Box::new(resolve_canonical_bitvector_shallow(right.start())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
            )
            && assumptions.conditions_equal_modulo_proven_snapshots(
                &ConditionTerm::Bitvector32Equal(
                    Box::new(resolve_canonical_bitvector_shallow(left.end())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                &ConditionTerm::Bitvector32Equal(
                    Box::new(resolve_canonical_bitvector_shallow(right.end())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
            )
    };
    ranges_equal(left_a, right_a) && ranges_equal(left_b, right_b)
        || ranges_equal(left_a, right_b) && ranges_equal(left_b, right_a)
}
