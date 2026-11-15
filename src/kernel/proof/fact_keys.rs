//! Structural index keys for persistent checked proof facts.
//!
//! MemoryState-blind keys select a small set of potentially transportable facts.
//! A key match is never proof authority: the checked state bridge still
//! validates every selected candidate.

#[cfg(test)]
use crate::kernel::CompareRelation;
use crate::kernel::LoadKind;
use crate::kernel::MachineUnaryOp;
use crate::kernel::unary_term;
use crate::kernel::{
    AlgebraicTerm, AlgebraicTermNode, AlgebraicValue, IntegerComparisonOperator, IntegerTerm,
    MachineIntegerType, PointerValue, ProgramType, ProgramValue, PureFunctionArgument,
    SharedIntegerTerm, SharedMemory, Sort, Term,
};
use crate::kernel::{
    BitvectorBinaryOp, BitvectorComparisonOp, BitvectorUnaryOp, ComparisonOperator, ConditionTerm,
    FloatClassification, FloatCondition, MachineTerm, MemoryRange, Pointer, PointerBlock,
    PointerOffsetTerm, Proposition, Variable,
};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int64_constant, native_constant,
    uint64_constant,
};
use num_bigint::BigInt;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
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
pub(crate) enum MemoryErasedPropositionKey {
    Condition(MemoryErasedConditionKey, bool),
    Implies(Box<Self>, Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    MemorySeparate(
        Box<MemoryErasedMemoryRangeKey>,
        Box<MemoryErasedMemoryRangeKey>,
    ),
    Exact(Proposition),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct MemoryErasedMemoryRangeKey {
    block: PointerBlock,
    offset: MemoryErasedPointerOffsetKey,
    start: MemoryErasedBitvectorKey,
    end: MemoryErasedBitvectorKey,
    wide: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum MemoryErasedConditionKey {
    PointerValueEqual(MemoryErasedPointerValueKey, MemoryErasedPointerValueKey),
    AlgebraicEqual(Box<AlgebraicTerm>, Box<AlgebraicTerm>),
    Constant(bool),
    Variable(Variable),
    Comparison(
        BitvectorComparisonOp,
        MemoryErasedBitvectorKey,
        MemoryErasedBitvectorKey,
    ),
    Float32(MemoryErasedFloatConditionKey),
    Float64(MemoryErasedFloatConditionKey),
    PointerOffsetEqual(MemoryErasedPointerOffsetKey, MemoryErasedPointerOffsetKey),
    PointerEqual(MemoryErasedPointerKey, MemoryErasedPointerKey),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum MemoryErasedFloatConditionKey {
    Comparison {
        operator: ComparisonOperator,
        left: MemoryErasedBitvectorKey,
        right: MemoryErasedBitvectorKey,
    },
    Classification {
        classification: FloatClassification,
        value: MemoryErasedBitvectorKey,
    },
}

#[allow(dead_code)]
mod fold_keys;
mod match_keys;
mod memory_operands;
mod pointer_keys;
use memory_operands::MemoryErasedBitvectorKey;
use pointer_keys::Canonical;

pub(crate) fn clear_state_operand_keys() {
    memory_operands::clear();
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct MemoryErasedPointerValueKey {
    program_type: ProgramType,
    address: MemoryErasedPointerKey,
    designation: MemoryErasedPointerKey,
    opaque_extent: Option<MemoryErasedPointerKey>,
    extent: Option<(MemoryErasedPointerKey, MemoryErasedBitvectorKey)>,
    extent_known: bool,
}

impl MemoryErasedPointerValueKey {
    fn requires_checked_match(&self) -> bool {
        self.address.requires_checked_match()
            || self.designation.requires_checked_match()
            || self
                .opaque_extent
                .as_ref()
                .is_some_and(MemoryErasedPointerKey::requires_checked_match)
            || self.extent.as_ref().is_some_and(|(start, width)| {
                start.requires_checked_match() || width.requires_checked_match()
            })
    }
}

fn memory_erased_pointer_value_key(pointer: &PointerValue) -> MemoryErasedPointerValueKey {
    MemoryErasedPointerValueKey {
        program_type: pointer.program_type(),
        address: memory_erased_pointer_key(pointer.pointer()),
        designation: memory_erased_pointer_key(pointer.designation()),
        opaque_extent: if pointer.extent_is_known() {
            None
        } else {
            pointer.opaque_extent().map(memory_erased_pointer_key)
        },
        extent: pointer.extent().map(|extent| {
            (
                memory_erased_pointer_key(&extent.start),
                memory_erased_bitvector_key(&extent.width),
            )
        }),
        extent_known: pointer.extent_is_known(),
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct MemoryErasedPointerKey {
    block: MemoryErasedPointerBlockKey,
    offset: Box<MemoryErasedPointerOffsetKey>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum MemoryErasedPointerBlockKey {
    Exact(PointerBlock),
    Read(Box<MemoryErasedPointerKey>),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) enum MemoryErasedPointerOffsetNode {
    Add(MemoryErasedPointerOffsetKey, MemoryErasedPointerOffsetKey),
    Int32Scaled {
        value: MemoryErasedBitvectorKey,
        byte_width: i64,
    },
    Int64Scaled {
        value: MemoryErasedBitvectorKey,
        byte_width: i64,
        unsigned: bool,
    },
    Exact(PointerOffsetTerm),
}

impl MemoryErasedPropositionKey {
    /// Index facts whose keys erase read states or address-origin
    /// annotations. Sharing a key selects candidates; the checked matcher
    /// still establishes their semantic identity.
    pub(crate) fn requires_checked_match(&self) -> bool {
        match self {
            Self::Condition(condition, _) => condition.requires_checked_match(),
            Self::Implies(left, right) | Self::And(left, right) | Self::Or(left, right) => {
                left.requires_checked_match() || right.requires_checked_match()
            }
            Self::Not(body) => body.requires_checked_match(),
            Self::MemorySeparate(left, right) => {
                let side = |key: &MemoryErasedMemoryRangeKey| {
                    key.offset.requires_checked_match()
                        || key.start.requires_checked_match()
                        || key.end.requires_checked_match()
                };
                side(left) || side(right)
            }
            Self::Exact(_) => false,
        }
    }
}

impl MemoryErasedConditionKey {
    fn requires_checked_match(&self) -> bool {
        match self {
            Self::AlgebraicEqual(_, _) => false,
            Self::PointerValueEqual(left, right) => {
                left.requires_checked_match() || right.requires_checked_match()
            }
            Self::Comparison(_, left, right) => {
                left.requires_checked_match() || right.requires_checked_match()
            }
            Self::Float32(condition) | Self::Float64(condition) => {
                condition.requires_checked_match()
            }
            Self::PointerOffsetEqual(left, right) => {
                left.requires_checked_match() || right.requires_checked_match()
            }
            Self::PointerEqual(left, right) => {
                left.requires_checked_match() || right.requires_checked_match()
            }
            Self::Constant(_) | Self::Variable(_) => false,
        }
    }
}

impl MemoryErasedFloatConditionKey {
    fn requires_checked_match(&self) -> bool {
        match self {
            Self::Comparison { left, right, .. } => {
                left.requires_checked_match() || right.requires_checked_match()
            }
            Self::Classification { value, .. } => value.requires_checked_match(),
        }
    }
}

impl MemoryErasedPointerKey {
    fn requires_checked_match(&self) -> bool {
        matches!(self.block, MemoryErasedPointerBlockKey::Read(_))
            || self.offset.requires_checked_match()
    }
}

type MemoryErasedPointerOffsetKey = Canonical<MemoryErasedPointerOffsetNode>;
type AlphaPointerOffsetKey = Canonical<AlphaPointerOffsetNode>;

impl MemoryErasedPointerOffsetNode {
    fn requires_checked_match(&self) -> bool {
        match self {
            Self::Add(left, right) => {
                left.requires_checked_match() || right.requires_checked_match()
            }
            Self::Int32Scaled { value, .. } | Self::Int64Scaled { value, .. } => {
                value.requires_checked_match()
            }
            Self::Exact(_) => false,
        }
    }
}

pub(crate) fn memory_erased_proposition_key(
    proposition: &Proposition,
) -> MemoryErasedPropositionKey {
    enum Frame<'a> {
        Visit(&'a Proposition),
        BuildImplies,
        BuildAnd,
        BuildOr,
        BuildNot,
    }

    if !matches!(
        proposition,
        Proposition::Implies(_, _)
            | Proposition::And(_, _)
            | Proposition::Or(_, _)
            | Proposition::Not(_)
    ) {
        return memory_erased_proposition_key_one(proposition);
    }

    let mut frames = vec![Frame::Visit(proposition)];
    let mut values = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Visit(proposition) => match proposition {
                Proposition::Implies(left, right) => {
                    frames.push(Frame::BuildImplies);
                    frames.push(Frame::Visit(right));
                    frames.push(Frame::Visit(left));
                }
                Proposition::And(left, right) => {
                    frames.push(Frame::BuildAnd);
                    frames.push(Frame::Visit(right));
                    frames.push(Frame::Visit(left));
                }
                Proposition::Or(left, right) => {
                    frames.push(Frame::BuildOr);
                    frames.push(Frame::Visit(right));
                    frames.push(Frame::Visit(left));
                }
                Proposition::Not(body) => {
                    frames.push(Frame::BuildNot);
                    frames.push(Frame::Visit(body));
                }
                proposition => values.push(memory_erased_proposition_key_one(proposition)),
            },
            Frame::BuildImplies => {
                let right = values.pop().expect("the implication consequent is keyed");
                let left = values.pop().expect("the implication antecedent is keyed");
                values.push(MemoryErasedPropositionKey::Implies(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            Frame::BuildAnd => {
                let right = values.pop().expect("the conjunction right side is keyed");
                let left = values.pop().expect("the conjunction left side is keyed");
                values.push(MemoryErasedPropositionKey::And(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            Frame::BuildOr => {
                let right = values.pop().expect("the disjunction right side is keyed");
                let left = values.pop().expect("the disjunction left side is keyed");
                values.push(MemoryErasedPropositionKey::Or(
                    Box::new(left),
                    Box::new(right),
                ));
            }
            Frame::BuildNot => {
                let body = values.pop().expect("the negated proposition is keyed");
                values.push(MemoryErasedPropositionKey::Not(Box::new(body)));
            }
        }
    }
    values.pop().expect("the root proposition is keyed")
}

fn memory_erased_proposition_key_one(proposition: &Proposition) -> MemoryErasedPropositionKey {
    match proposition {
        Proposition::ConditionIs(
            condition @ crate::kernel::integer_comparison_condition!(_, _),
            value,
        ) => state_observation_key(condition, *value)
            .map(|(key, value)| MemoryErasedPropositionKey::Condition(key, value))
            .unwrap_or_else(|| MemoryErasedPropositionKey::Exact(proposition.clone())),
        // `Bool` values have no state-blind key yet: they are filed
        // exactly until their checked memory bridge has a structural view.
        Proposition::ConditionIs(condition, _) if condition.is_bool_value_form() => {
            MemoryErasedPropositionKey::Exact(proposition.clone())
        }
        Proposition::ConditionIs(condition, value) => {
            MemoryErasedPropositionKey::Condition(memory_erased_condition_key(condition), *value)
        }
        Proposition::Implies(left, right) => MemoryErasedPropositionKey::Implies(
            Box::new(memory_erased_proposition_key(left)),
            Box::new(memory_erased_proposition_key(right)),
        ),
        Proposition::And(left, right) => MemoryErasedPropositionKey::And(
            Box::new(memory_erased_proposition_key(left)),
            Box::new(memory_erased_proposition_key(right)),
        ),
        Proposition::Or(left, right) => MemoryErasedPropositionKey::Or(
            Box::new(memory_erased_proposition_key(left)),
            Box::new(memory_erased_proposition_key(right)),
        ),
        Proposition::Not(body) => {
            MemoryErasedPropositionKey::Not(Box::new(memory_erased_proposition_key(body)))
        }
        Proposition::ResourceSeparate { .. } if proposition.memory_separation().is_some() => {
            let (left, right) = proposition
                .memory_separation()
                .expect("the guard matched a memory separation");
            MemoryErasedPropositionKey::MemorySeparate(
                memory_erased_memory_range_key(left),
                memory_erased_memory_range_key(right),
            )
        }
        proposition => MemoryErasedPropositionKey::Exact(proposition.clone()),
    }
}

fn memory_erased_memory_range_key(range: &MemoryRange) -> Box<MemoryErasedMemoryRangeKey> {
    Box::new(MemoryErasedMemoryRangeKey {
        block: range.base().block.clone(),
        offset: memory_erased_pointer_offset_key(&range.base().offset),
        start: memory_erased_bitvector_key(range.bound_terms().0),
        end: memory_erased_bitvector_key(range.bound_terms().1),
        // One untyped term can bound a range of either kind, and the two
        // are different ranges.
        wide: range.wide_bounds().is_some(),
    })
}

/// Candidate identity for a legacy nonoverflow premise, read from retained
/// query operands. Matching this key alone never supplies memory authority.
pub(super) fn memory_erased_nonoverflow_key(
    query: &crate::kernel::machine_integer::definedness::OverflowQueryView,
) -> MemoryErasedPropositionKey {
    MemoryErasedPropositionKey::Condition(
        MemoryErasedConditionKey::Comparison(
            BitvectorComparisonOp::Overflows(query.format, query.operation_kind()),
            memory_operands::operand(query.operands[0].operand_view()),
            memory_operands::operand(query.operands[1].operand_view()),
        ),
        false,
    )
}

fn state_observation_key(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(MemoryErasedConditionKey, bool)> {
    use crate::kernel::CompareRelation as R;
    use crate::kernel::machine_integer::{
        Relation,
        comparison::{FactOperand, fact_operand_identity, native_comparison_view},
    };
    let view = native_comparison_view(condition, value)?;
    let (relation, truth) = match view.relation {
        Relation::Equal => (R::Equal, true),
        Relation::NotEqual => (R::Equal, false),
        Relation::Less => (R::LessThan, true),
        Relation::LessEqual => (R::LessEqual, true),
    };
    let (format, sides) = fact_operand_identity(
        view.format,
        relation,
        view.operands
            .each_ref()
            .map(|operand| operand.operand_view()),
    );
    let [left, right] = sides.map(|side| match side {
        FactOperand::Term(view) => memory_operands::operand(view),
        FactOperand::Value(value) => {
            memory_erased_bitvector_key(&MachineTerm::narrow_constant(format, value as u128))
        }
    });
    Some((
        MemoryErasedConditionKey::Comparison(
            BitvectorComparisonOp::Compare(format, relation),
            left,
            right,
        ),
        truth,
    ))
}

fn memory_erased_boolean_operand_key(
    condition: crate::kernel::BooleanOperandView<'_>,
) -> MemoryErasedConditionKey {
    use crate::kernel::machine_integer::comparison::{FactOperand, fact_operand_identity};
    if let Some((format, relation, operands)) = condition.comparison() {
        let (format, operands) = fact_operand_identity(format, relation, operands);
        let [left, right] = operands.map(|operand| match operand {
            FactOperand::Term(term) => memory_operands::operand(term),
            FactOperand::Value(value) => memory_erased_bitvector_key(
                &crate::kernel::ComparisonSide::Value(value).term(format),
            ),
        });
        return MemoryErasedConditionKey::Comparison(
            BitvectorComparisonOp::Compare(format, relation),
            left,
            right,
        );
    }
    if let Some((format, operation, [a, b])) = condition.overflow() {
        return MemoryErasedConditionKey::Comparison(
            BitvectorComparisonOp::Overflows(format, operation),
            memory_operands::operand(a),
            memory_operands::operand(b),
        );
    }
    if let Some([a, b]) = condition.pointer_offsets() {
        return MemoryErasedConditionKey::PointerOffsetEqual(
            pointer_keys::state_offset(&a),
            pointer_keys::state_offset(&b),
        );
    }
    if let Some([a, b]) = condition.pointer_values() {
        return MemoryErasedConditionKey::PointerValueEqual(
            pointer_keys::recorded_value(&a),
            pointer_keys::recorded_value(&b),
        );
    }
    if let Some([a, b]) = condition.pointer_addresses() {
        return MemoryErasedConditionKey::PointerEqual(
            pointer_keys::state_address(&a),
            pointer_keys::state_address(&b),
        );
    }
    memory_erased_condition_key(&condition.native())
}

fn memory_erased_condition_key(condition: &ConditionTerm) -> MemoryErasedConditionKey {
    // Keyed at the fact identity: a native 8- or 16-bit comparison and the
    // `int32` comparison of its widenings are one fact.
    if let Some((operator, left, right)) = condition.as_fact_comparison() {
        return MemoryErasedConditionKey::Comparison(
            operator,
            memory_erased_bitvector_key(&left),
            memory_erased_bitvector_key(&right),
        );
    }
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => {
            MemoryErasedConditionKey::PointerValueEqual(
                memory_erased_pointer_value_key(left),
                memory_erased_pointer_value_key(right),
            )
        }

        ConditionTerm::Constant(value) => MemoryErasedConditionKey::Constant(*value),
        ConditionTerm::AlgebraicEqual(left, right) => {
            MemoryErasedConditionKey::AlgebraicEqual(left.clone(), right.clone())
        }
        ConditionTerm::Variable(variable) => MemoryErasedConditionKey::Variable(*variable),
        ConditionTerm::Float32(float_condition) => {
            MemoryErasedConditionKey::Float32(memory_erased_float_condition_key(float_condition))
        }
        ConditionTerm::Float64(float_condition) => {
            MemoryErasedConditionKey::Float64(memory_erased_float_condition_key(float_condition))
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            MemoryErasedConditionKey::PointerOffsetEqual(
                memory_erased_pointer_offset_key(left),
                memory_erased_pointer_offset_key(right),
            )
        }
        ConditionTerm::PointerEqual(left, right) => MemoryErasedConditionKey::PointerEqual(
            memory_erased_pointer_key(left),
            memory_erased_pointer_key(right),
        ),
        crate::kernel::ConditionTerm::Compare { .. }
        | crate::kernel::ConditionTerm::Overflows { .. } => {
            unreachable!("bitvector comparisons are keyed above")
        }
        crate::kernel::integer_comparison_condition!(_, _) => {
            unreachable!("integer conditions use the exact proposition index")
        }
        ConditionTerm::BoolApplication(_)
        | ConditionTerm::BoolIf { .. }
        | ConditionTerm::BoolEqual(..)
        | ConditionTerm::BoolLoad(..) => {
            unreachable!("`Bool` values use the exact proposition index")
        }
    }
}

fn memory_erased_float_condition_key(condition: &FloatCondition) -> MemoryErasedFloatConditionKey {
    match condition {
        FloatCondition::Comparison {
            operator,
            left,
            right,
        } => MemoryErasedFloatConditionKey::Comparison {
            operator: *operator,
            left: memory_erased_bitvector_key(left),
            right: memory_erased_bitvector_key(right),
        },
        FloatCondition::Classification {
            classification,
            value,
        } => MemoryErasedFloatConditionKey::Classification {
            classification: *classification,
            value: memory_erased_bitvector_key(value),
        },
    }
}

fn memory_erased_bitvector_key(term: &MachineTerm) -> MemoryErasedBitvectorKey {
    memory_operands::written(term)
}

thread_local! {
    static POINTER_READ_KEY_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

struct PointerReadKeyDepth(usize);
impl Drop for PointerReadKeyDepth {
    fn drop(&mut self) {
        POINTER_READ_KEY_DEPTH.with(|depth| depth.set(self.0));
    }
}

fn memory_erased_pointer_key(pointer: &Pointer) -> MemoryErasedPointerKey {
    let depth = POINTER_READ_KEY_DEPTH.with(|depth| depth.replace(depth.get() + 1));
    let _restore = PointerReadKeyDepth(depth);
    // This candidate key forgets states, never proof authority. Bound
    // registry expansion across both defining addresses and their offsets.
    let read = match &pointer.block {
        PointerBlock::LoadedPointer(_) if depth < 3 => {
            pointer.as_loaded_value().map(|read| read.defining_address)
        }
        PointerBlock::Symbolic(variable) if depth < 3 => {
            crate::kernel::registered_load_for_variable(variable).map(|(_, source)| source)
        }
        _ => None,
    };
    MemoryErasedPointerKey {
        block: read
            .map(|source| {
                MemoryErasedPointerBlockKey::Read(Box::new(memory_erased_pointer_key(&source)))
            })
            .unwrap_or_else(|| MemoryErasedPointerBlockKey::Exact(pointer.block.clone())),
        offset: Box::new(memory_erased_pointer_offset_key(&pointer.offset)),
    }
}

fn memory_erased_pointer_offset_key(offset: &PointerOffsetTerm) -> MemoryErasedPointerOffsetKey {
    Canonical::new(match offset {
        PointerOffsetTerm::Add(left, right) => MemoryErasedPointerOffsetNode::Add(
            memory_erased_pointer_offset_key(left),
            memory_erased_pointer_offset_key(right),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            MemoryErasedPointerOffsetNode::Int32Scaled {
                value: memory_operands::operand(value.operand_view()),
                byte_width: *byte_width,
            }
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => MemoryErasedPointerOffsetNode::Int64Scaled {
            value: memory_operands::operand(value.operand_view()),
            byte_width: *byte_width,
            unsigned: *unsigned,
        },
        offset => MemoryErasedPointerOffsetNode::Exact(offset.clone()),
    })
}

/// Alpha-invariant key for the quantified logical/condition fragment used by
/// checked premises. Bound variables use structural ordinals and free
/// variables retain their kernel identities. Raw bitvector loads outside a
/// loadability atom remain state-blind on this selection path, while a
/// `MemoryLoadable` atom retains the exact state that is part of its
/// checked premise.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct QuantifiedEquivalenceKey(AlphaPropositionKey);

/// Structural identity for a stated proposition.  Unlike the older
/// state-blind selection key, this key retains the identity of every
/// memory state named by a load.  Bound variables are represented by their
/// structural ordinal while free variables retain their kernel identity.
///
/// The key is intentionally private in shape: callers can use it for exact
/// indexed lookup, but cannot manufacture one without walking a checked
/// proposition through [`proposition_identity_key`].
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(crate) struct PropositionIdentityKey(AlphaPropositionKey);

/// Candidate selector for pointer congruence. Pointer values are holes, but
/// their types and positions, other arguments, and memory versions remain in
/// the selector. It is a shallow fingerprint, never evidence: the consumer checks every
/// non-pointer argument exactly and every typed pointer through the graph.
pub(in crate::kernel) fn pointer_predicate_selector(proposition: &Proposition) -> Option<u64> {
    let Proposition::Predicate { name, arguments } = proposition else {
        return None;
    };
    let arguments = arguments
        .iter()
        .map(|argument| match argument {
            Term::ProgramValue(ProgramValue::Pointer(pointer)) => Term::ProgramValue(
                ProgramValue::typed_pointer(crate::kernel::Pointer::null(), pointer.program_type()),
            ),
            other => other.clone(),
        })
        .collect();
    let key = proposition_identity_key(&Proposition::Predicate {
        name: name.clone(),
        arguments,
    })?;
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    key.hash(&mut hasher);
    Some(hasher.finish())
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPropositionKey {
    EqualBitvector(AlphaBitvectorKey, AlphaBitvectorKey),
    EqualAlgebraic(AlphaAlgebraicKey, AlphaAlgebraicKey),
    Condition(AlphaConditionKey, bool),
    Predicate {
        name: String,
        arguments: Vec<AlphaPredicateArgumentKey>,
    },
    MemoryReadDefined {
        memory: AlphaStateKey,
        pointer: AlphaPointerKey,
        value_type: ProgramType,
    },
    MemoryLoadable {
        memory: AlphaStateKey,
        base: AlphaPointerKey,
        bytes: AlphaBitvectorKey,
        wide: bool,
    },
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    Implies(Box<Self>, Box<Self>),
    ForAll(Sort, Box<Self>),
    Exists(Sort, Box<Self>),
}

/// A predicate argument's bounded selector key. A `ExecutionState` uses its memory
/// identity to narrow the bucket; the final quantified-fact comparison also
/// checks its non-memory storage without copying the whole state into a key.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPredicateArgumentKey {
    StateMemory(AlphaStateKey),
    Memory(AlphaStateKey),
    Value(AlphaProgramValueKey),
    Integer(AlphaIntegerKey),
    Algebraic(AlphaAlgebraicKey),
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
/// state-aware alpha boundary for equality and inequality premises.
pub(crate) type IntegerEqualityAlphaKey = IntegerConditionAlphaKey;

/// Alpha key used by the checked fact index for root range-fold Integer
/// comparison atoms.
///
/// Integer range-fold binders are canonicalized by a typed alpha environment.
/// Load-bearing C payloads retain their exact `SharedMemory` identities, so
/// this index is authoritative only for comparisons whose loads name the same
/// states. The entry point is deliberately narrow: only a true Integer
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
        crate::kernel::integer_comparison_condition!(left, right) => (left, right),
        _ => return None,
    };
    if !matches!(left.as_ref(), IntegerTerm::RangeFold { .. })
        && !matches!(right.as_ref(), IntegerTerm::RangeFold { .. })
    {
        return None;
    }
    let comparison = super::term_rewrite::TermRewrite::arithmetic_comparison(proposition);
    if crate::instrumentation::deadline_exceeded() {
        return None;
    }
    state_alpha_proposition_key(comparison.as_ref().unwrap_or(proposition))
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

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaBitvectorKey {
    AlgebraicMatch(Box<AlphaAlgebraicKey>, Vec<match_keys::Arm>),
    Constant(u32),
    Int64Constant(i64),
    UInt64Constant(u64),
    MachineIntegerConstant(crate::kernel::MachineIntegerConstant),
    Variable(AlphaVariableKey),
    Binary(BitvectorBinaryOp, Box<Self>, Box<Self>),
    BitwiseNot(Box<Self>),
    Unary(MachineIntegerType, MachineUnaryOp, Box<Self>),
    Float32Negate(Box<Self>),
    Float64Negate(Box<Self>),
    If {
        condition: Box<AlphaConditionKey>,
        then_term: Box<Self>,
        else_term: Box<Self>,
    },
    RangeFold {
        start: Box<AlphaMachineKey>,
        end: Box<AlphaMachineKey>,
        initial: Box<AlphaMachineKey>,
        body: Box<AlphaMachineKey>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<Self>,
    },
    ClickFunctionApplication {
        name: String,
        arguments: Vec<AlphaPureFunctionArgumentKey>,
    },
    Load(Box<AlphaPointerKey>, LoadKind),
    RegisteredLoad(AlphaRegisteredLoadId),
    Address(Box<AlphaPointerKey>),
    IntegerToMachine(MachineIntegerType, AlphaIntegerKey),
    MachineIntegerCast(MachineIntegerType, MachineIntegerType, Box<Self>),
    BoolCast(MachineIntegerType, Box<AlphaConditionKey>),
    Int64From32(Box<Self>),
    UInt64From32(Box<Self>),
    UInt32From64(Box<Self>),
    Int64FromUInt32(Box<Self>),
    UInt64FromInt32(Box<Self>),
    UInt64FromInt64(Box<Self>),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPureFunctionArgumentKey {
    Value(AlphaProgramValueKey),
    Integer(AlphaIntegerKey),
    Algebraic(AlphaAlgebraicKey),
    ArrayRef {
        memory: AlphaStateKey,
        pointer: AlphaProgramValueKey,
        element_type: ProgramType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaProgramValueKey {
    Void,
    /// A value of a specification type, keyed as the algebraic term it is.
    Parameter(Box<AlphaAlgebraicKey>),
    Scalar(ProgramType, AlphaMachineKey),
    Pointer {
        program_type: ProgramType,
        pointee_volatile: bool,
        pointee_constant: bool,
        pointer: AlphaPointerKey,
        designation: AlphaPointerKey,
        extent_known: bool,
        opaque_extent: Option<AlphaPointerKey>,
        /// The subobject extent's start key and byte width.
        extent: Option<(AlphaPointerKey, AlphaMachineKey)>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaAlgebraicKey {
    Variable(crate::kernel::AlgebraicType, AlphaVariableKey),
    Constructor {
        algebraic_type: crate::kernel::AlgebraicType,
        variant: String,
        fields: Vec<AlphaAlgebraicValueKey>,
    },
    /// A function's algebraic result, such as the slice a library iterator
    /// yields at an index: a binder among its arguments renames.
    PureFunctionApplication {
        algebraic_type: crate::kernel::AlgebraicType,
        name: String,
        arguments: Vec<AlphaPureFunctionArgumentKey>,
    },
    /// A library value read from memory, such as a borrowed Rust iterator:
    /// keyed by the scalar load at the same memory and address, exactly as
    /// that load is.
    MemoryLoad {
        algebraic_type: crate::kernel::AlgebraicType,
        carrier: AlphaBitvectorKey,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaAlgebraicValueKey {
    Program(AlphaProgramValueKey),
    Integer(AlphaIntegerKey),
    Algebraic(AlphaAlgebraicKey),
}

/// O(1) identity for a retained memory state.
///
/// A same-arena `(arena, id)` pair is the exact identity assigned by the
/// immutable memory arena.  Handles are retained so the identity cannot be
/// observed after its backing state has been dropped.  Cross-arena
/// states deliberately compare unequal: structural equality there would
/// scan the complete memory, so the exact authority falls back to its normal
/// proof path instead of consulting unrelated heap/history state.
#[derive(Clone)]
struct AlphaStateKey {
    identity: (u32, u32),
    _state: SharedMemory,
}

impl AlphaStateKey {
    fn new(retained_state: &SharedMemory) -> Self {
        Self {
            identity: retained_state.arena_id(),
            _state: retained_state.clone(),
        }
    }
}

impl fmt::Debug for AlphaStateKey {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_tuple("AlphaStateKey")
            .field(&self.identity)
            .finish()
    }
}

impl PartialEq for AlphaStateKey {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}

impl Eq for AlphaStateKey {}

impl PartialOrd for AlphaStateKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AlphaStateKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity.cmp(&other.identity)
    }
}

impl Hash for AlphaStateKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPointerOffsetNode {
    Constant(i64),
    Variable(AlphaVariableKey),
    Add(AlphaPointerOffsetKey, AlphaPointerOffsetKey),
    RegisteredLoad(AlphaRegisteredLoadId),
    Int32Scaled {
        value: Canonical<AlphaMachineKey>,
        byte_width: i64,
    },
    Int64Scaled {
        value: Canonical<AlphaMachineKey>,
        byte_width: i64,
        unsigned: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaPointerBlockKey {
    Concrete(String),
    StringLiteral {
        identity: String,
        bytes: Vec<u8>,
    },
    Function(String),
    FunctionSymbolic(AlphaVariableKey),
    ExternalArgument,
    ExternalObject(AlphaVariableKey),
    Symbolic(AlphaVariableKey),
    LoadedPointer(crate::kernel::PointerLoadId),
    /// A pointer loaded from memory is its own block, named by the load
    /// variable; like a load at an offset position, it is keyed by the
    /// state and address it reads, so a binder inside that address
    /// renames.
    RegisteredLoad(AlphaRegisteredLoadId),
    /// A pointer read named by its `PointerLoadId`, keyed like
    /// `RegisteredLoad` by the state and address it reads; a distinct
    /// variant so it never meets a scalar load's key.
    LoadedRead(AlphaRegisteredLoadId),
    Heap(u64),
    Temporary(u64),
    /// A function's pointer result, such as a slice's data pointer: a binder
    /// among its arguments renames.
    PureFunctionApplication {
        name: String,
        arguments: Vec<AlphaPureFunctionArgumentKey>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct AlphaPointerKey {
    block: AlphaPointerBlockKey,
    offset: AlphaPointerOffsetKey,
}

/// A compact reference to one live canonical registered-load node. The node
/// owns its state and its immediate pointer descriptor, while nested load
/// references own only their child nodes. This makes each key retain exactly
/// the reachable load DAG; the process-local interner stores weak records and
/// cannot keep unrelated states alive after their keys are dropped.
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
    interner: Arc<std::sync::Mutex<AlphaRegisteredLoadInterner>>,
    fingerprint: u64,
    retained_state: AlphaStateKey,
    pointer: AlphaPointerKey,
    kind: LoadKind,
}

/// Weak entries by descriptor fingerprint. A record removes its own entry
/// when it dies, so interning one load costs only its own bucket and never
/// revisits records that an unrelated proof's memos keep alive.
struct AlphaRegisteredLoadInterner {
    buckets: HashMap<u64, Vec<Weak<AlphaRegisteredLoadRecord>>>,
}

impl Drop for AlphaRegisteredLoadRecord {
    fn drop(&mut self) {
        // The only holder of the lock is an intern call on this thread, which
        // drops no last reference while holding it; if another thread's drop
        // races one, the dead entry stays until that bucket is next interned,
        // which retains only live candidates.
        //
        // This charges no work: records also drop while thread-local memo
        // tables are destroyed, after the instrumentation tables are gone,
        // and the scan is of the bucket this record's intern already paid
        // to scan.
        let Ok(mut interner) = self.interner.try_lock() else {
            return;
        };
        let Some(bucket) = interner.buckets.get_mut(&self.fingerprint) else {
            return;
        };
        bucket.retain(|candidate| candidate.strong_count() != 0);
        if bucket.is_empty() {
            interner.buckets.remove(&self.fingerprint);
        }
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
        }));
        *cell.borrow_mut() = Arc::downgrade(&interner);
        Some(interner)
    })
}

fn alpha_registered_load_descriptor_fingerprint(
    retained_state: &AlphaStateKey,
    pointer: &AlphaPointerKey,
    kind: LoadKind,
) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    retained_state.hash(&mut hasher);
    pointer.hash(&mut hasher);
    kind.hash(&mut hasher);
    hasher.finish()
}

fn intern_alpha_registered_load(
    interner: &Arc<std::sync::Mutex<AlphaRegisteredLoadInterner>>,
    retained_state: AlphaStateKey,
    pointer: AlphaPointerKey,
    kind: LoadKind,
) -> Option<AlphaRegisteredLoadId> {
    let fingerprint = alpha_registered_load_descriptor_fingerprint(&retained_state, &pointer, kind);
    let mut interner_state = interner.lock().ok()?;
    let bucket = interner_state.buckets.entry(fingerprint).or_default();
    if crate::instrumentation::deadline_exceeded_with_work(bucket.len().max(1)) {
        return None;
    }
    bucket.retain(|candidate| candidate.strong_count() != 0);
    for candidate in bucket.iter() {
        let Some(record) = candidate.upgrade() else {
            continue;
        };
        if record.retained_state == retained_state
            && record.pointer == pointer
            && record.kind == kind
        {
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
        interner: interner.clone(),
        fingerprint,
        retained_state,
        pointer,
        kind,
    });
    bucket.push(Arc::downgrade(&record));
    Some(AlphaRegisteredLoadId(record))
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaConditionKey {
    AlgebraicEqual(Box<AlphaAlgebraicKey>, Box<AlphaAlgebraicKey>),
    PointerValueEqual(Box<AlphaProgramValueKey>, Box<AlphaProgramValueKey>),
    Constant(bool),
    Variable(AlphaVariableKey),
    Binary(BitvectorComparisonOp, AlphaBitvectorKey, AlphaBitvectorKey),
    PointerOffsetEqual(AlphaPointerOffsetKey, AlphaPointerOffsetKey),
    PointerEqual(AlphaPointerKey, AlphaPointerKey),
    IntegerComparison(IntegerComparisonOperator, AlphaIntegerKey, AlphaIntegerKey),
    MachineComparison(MachineIntegerType, u8, AlphaMachineKey, AlphaMachineKey),
    /// The `Bool` value forms (Stage 5).
    BoolApplication {
        name: String,
        arguments: Vec<AlphaPureFunctionArgumentKey>,
    },
    BoolIf(Box<Self>, Box<Self>, Box<Self>),
    BoolEqual(Box<Self>, Box<Self>),
}

/// A locally interned DAG: equal repeated children are visited once and never
/// copied into a tree. Leaf keys preserve the existing binder/load authority.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct AlphaMachineKey {
    nodes: Vec<AlphaMachineNode>,
    root: usize,
}
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaMachineNode {
    Leaf(AlphaBitvectorKey),
    If(Box<AlphaConditionKey>, [usize; 2]),
    Binary(
        MachineIntegerType,
        crate::kernel::MachineBinaryOp,
        [usize; 2],
    ),
    Unary(MachineIntegerType, MachineUnaryOp, usize),
    Cast(u8, MachineIntegerType, MachineIntegerType, usize),
}

fn alpha_machine_key<const ALLOW_LOADS: bool>(
    view: crate::kernel::MachineOperandView<'_>,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaMachineKey> {
    use crate::kernel::{KernelTermNode as N, MachineOperandView as V};
    fn node<const ALLOW_LOADS: bool>(
        view: V<'_>,
        bindings: &mut AlphaBindings,
        next_binder: &mut usize,
        memo: &mut HashMap<u64, usize>,
        intern: &mut HashMap<AlphaMachineNode, usize>,
        nodes: &mut Vec<AlphaMachineNode>,
    ) -> Option<usize> {
        let shared_id = match view {
            V::Shared(term) => Some(term.id()),
            V::Legacy(_) => None,
        };
        if let Some(id) = shared_id.and_then(|id| memo.get(&id)) {
            return Some(*id);
        }
        alpha_work_checkpoint(bindings, 1)?;
        let mut child =
            |view| node::<ALLOW_LOADS>(view, bindings, next_binder, memo, intern, nodes);
        let value = if let Some((condition, [left, right])) = view.conditional() {
            let arms = [child(left)?, child(right)?];
            let outer_next_binder = *next_binder;
            let condition = alpha_condition_key_with_bindings::<ALLOW_LOADS>(
                &condition,
                bindings,
                next_binder,
            )?;
            *next_binder = outer_next_binder;
            AlphaMachineNode::If(Box::new(condition), arms)
        } else if let Some((format, operator, arguments)) = view.binary() {
            AlphaMachineNode::Binary(
                format,
                operator,
                [child(arguments[0])?, child(arguments[1])?],
            )
        } else if let Some((encoding, source, destination, operand)) = view.cast() {
            AlphaMachineNode::Cast(encoding as u8, source, destination, child(operand)?)
        } else {
            let unary = match view {
                V::Shared(term) => match term.node() {
                    N::MachineUnary {
                        format,
                        operator,
                        operand,
                    } => Some((*format, *operator, V::Shared(operand))),
                    _ => None,
                },
                V::Legacy(MachineTerm::Unary {
                    format,
                    op,
                    operand,
                }) => Some((*format, *op, V::Legacy(operand))),
                _ => None,
            };
            if let Some((format, operator, operand)) = unary {
                AlphaMachineNode::Unary(format, operator, child(operand)?)
            } else {
                // Binders introduced inside an opaque machine leaf are local
                // to that leaf. Reuse their ordinals across sibling leaves so
                // a repeated DAG child and repeated native syntax have the
                // same key; neither may advance the enclosing binder scope.
                let outer_next_binder = *next_binder;
                let leaf = match view {
                    V::Legacy(term) => alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                        term,
                        bindings,
                        next_binder,
                    )?,
                    V::Shared(root) if matches!(root.node(), N::Match(_)) => {
                        let N::Match(matched) = root.node() else {
                            unreachable!()
                        };
                        match_keys::retained_machine::<ALLOW_LOADS>(matched, bindings, next_binder)?
                    }
                    V::Shared(root) if matches!(root.node(), N::Fold(_)) => {
                        let N::Fold(fold) = root.node() else {
                            unreachable!()
                        };
                        fold_keys::machine_fold_key::<ALLOW_LOADS>(
                            fold.arguments.each_ref().map(V::Shared),
                            fold.accumulator,
                            fold.item,
                            bindings,
                            next_binder,
                        )?
                    }
                    V::Shared(root) if root.machine_read_leaf().is_some() => {
                        alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                            root.machine_read_leaf().expect("read leaf"),
                            bindings,
                            next_binder,
                        )?
                    }
                    V::Shared(root) if root.machine_conversion_leaf().is_some() => {
                        alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                            root.machine_conversion_leaf().expect("conversion leaf"),
                            bindings,
                            next_binder,
                        )?
                    }
                    V::Shared(_) => {
                        let term = if let Some(variable) = view.variable() {
                            MachineTerm::Variable(*variable)
                        } else {
                            view.literal()?
                        };
                        alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                            &term,
                            bindings,
                            next_binder,
                        )?
                    }
                };
                *next_binder = outer_next_binder;
                AlphaMachineNode::Leaf(leaf)
            }
        };
        let id = if let Some(id) = intern.get(&value) {
            *id
        } else {
            let id = nodes.len();
            intern.insert(value.clone(), id);
            nodes.push(value);
            id
        };
        if let Some(shared_id) = shared_id {
            memo.insert(shared_id, id);
        }
        Some(id)
    }
    let mut nodes = Vec::new();
    let root = node::<ALLOW_LOADS>(
        view,
        bindings,
        next_binder,
        &mut HashMap::new(),
        &mut HashMap::new(),
        &mut nodes,
    )?;
    Some(AlphaMachineKey { nodes, root })
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct AlphaIntegerKey {
    nodes: Vec<AlphaIntegerNode>,
    root: usize,
}

/// Opaque, exact alpha identity for one root Integer range fold.
///
/// The inner node graph retains carrier-aware binders and, in the state
/// aware mode, the `SharedMemory` handles named by load-bearing C payloads.
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
    Machine(MachineIntegerType, AlphaMachineKey),
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
    /// An `Integer`-valued specification function applied to arguments,
    /// keyed like the machine-valued application in [`AlphaBitvectorKey`].
    PureFunctionApplication {
        name: String,
        arguments: Vec<AlphaPureFunctionArgumentKey>,
    },
    /// A conditional, keyed like the machine conditional in
    /// [`AlphaBitvectorKey`].
    If {
        condition: Box<AlphaConditionKey>,
        then_term: usize,
        else_term: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum AlphaIntegerRangeIndex {
    Int32(AlphaMachineKey, AlphaMachineKey),
    UInt64(AlphaMachineKey, AlphaMachineKey),
    Integer(usize, usize),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum IntegerTermBinaryOp {
    Add,
    Subtract,
    Multiply,
    TruncatingQuotient,
    TruncatingRemainder,
}

fn alpha_integer_key(
    term: &IntegerTerm,
    bindings: &mut BTreeMap<Variable, usize>,
) -> Option<AlphaIntegerKey> {
    let mut environment = AlphaBindings {
        integer: bindings.clone(),
        bitvector: BTreeMap::new(),
        algebraic: BTreeMap::new(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        state_aware: false,
        raw_state_load_seen: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        pointer_load_stack: BTreeSet::new(),
        pointer_load_memo: HashMap::new(),
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

/// Build the exact state-aware alpha identity used by fold comparisons.
/// Only a root `IntegerTerm::RangeFold` is admitted; callers needing a larger
/// expression retain the ordinary proof path instead of treating a partial
/// key as authority.
pub(crate) fn integer_fold_alpha_key(term: &SharedIntegerTerm) -> Option<IntegerFoldAlphaKey> {
    if !matches!(term.as_ref(), IntegerTerm::RangeFold { .. }) {
        return None;
    }
    let mut environment = fold_keys::bindings();
    let mut next_binder = 0;
    alpha_integer_key_with_bindings(term.as_ref(), &mut environment, &mut next_binder).map(|key| {
        IntegerFoldAlphaKey {
            key,
            work_units: environment.work_units,
        }
    })
}

/// Whether two int32-carrier range folds are the same term up to their bound
/// accumulator and item variables.
///
/// This is [`integer_terms_alpha_equivalent`]'s int32 counterpart and shares
/// its whole implementation: the state-aware alpha key builder. That
/// builder gives every binder occurrence a structural ordinal
/// ([`AlphaVariableKey::Bound`]) and every free occurrence its own identity
/// ([`AlphaVariableKey::Free`]), so a variable bound in one fold can never
/// match a free variable of the same id in the other — which is exactly the
/// distinction a `left == right` name comparison loses. Binders are restored
/// when a nested fold's body is finished, so shadowing is handled too.
///
/// Only a root `MachineTerm::RangeFold` on each side is admitted. A
/// caller with anything else, or a term outside the key builder's supported
/// fragment (an opaque Click function application, an algebraic match), or
/// one whose key exhausts the work budget, gets `None` and keeps its ordinary
/// proof path rather than treating a partial key as authority.
pub(crate) fn bitvector_folds_alpha_equivalent(
    left: &MachineTerm,
    right: &MachineTerm,
) -> Option<bool> {
    let (left_key, left_work) = bitvector_fold_alpha_key(left)?;
    let (right_key, right_work) = bitvector_fold_alpha_key(right)?;
    if crate::instrumentation::deadline_exceeded_with_work(left_work.saturating_add(right_work)) {
        return None;
    }
    Some(left_key == right_key)
}

/// Compare bodies under their own binders after the caller has checked the
/// bounds and initial values equal. Reindex at the right outer operands, as
/// the native fold congruence rule does; this function proves no endpoint equality.
pub(crate) fn machine_fold_bodies_alpha_equivalent(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
) -> Option<bool> {
    let (la, li, left) = left.fold()?;
    let (ra, ri, right) = right.fold()?;
    let key = |a, i, body| {
        let mut environment = fold_keys::bindings();
        let key = fold_keys::machine_fold_key::<false>(
            [right[0], right[1], right[2], body],
            a,
            i,
            &mut environment,
            &mut 0,
        )?;
        Some((key, environment.work_units))
    };
    let (left, lw) = key(la, li, left[3])?;
    let (right, rw) = key(ra, ri, right[3])?;
    if crate::instrumentation::deadline_exceeded_with_work(lw.saturating_add(rw)) {
        return None;
    }
    Some(left == right)
}

/// Build the state-aware alpha identity of one int32 range fold, with the
/// work its construction charged. Mirrors [`integer_fold_alpha_key`].
fn bitvector_fold_alpha_key(term: &MachineTerm) -> Option<(AlphaBitvectorKey, usize)> {
    if !matches!(term, MachineTerm::RangeFold { .. }) {
        return None;
    }
    let mut environment = fold_keys::bindings();
    let mut next_binder = 0;
    let key = alpha_bitvector_key_with_bindings::<false>(term, &mut environment, &mut next_binder)?;
    Some((key, environment.work_units))
}

struct AlphaBindings {
    algebraic: BTreeMap<Variable, usize>,
    integer: BTreeMap<Variable, usize>,
    bitvector: BTreeMap<Variable, usize>,
    integer_scope: u64,
    bitvector_scope: u64,
    next_scope_id: u64,
    state_aware: bool,
    raw_state_load_seen: bool,
    registered_load_stack: BTreeSet<Variable>,
    registered_load_memo: HashMap<(Variable, u64, u64, usize), (AlphaRegisteredLoadId, usize)>,
    pointer_load_stack: BTreeSet<crate::kernel::PointerLoadId>,
    pointer_load_memo:
        HashMap<(crate::kernel::PointerLoadId, u64, u64, usize), (AlphaRegisteredLoadId, usize)>,
    load_interner: Option<Arc<std::sync::Mutex<AlphaRegisteredLoadInterner>>>,
    work_units: usize,
}

fn alpha_work_checkpoint(bindings: &mut AlphaBindings, units: usize) -> Option<()> {
    bindings.work_units = bindings.work_units.saturating_add(units);
    let exhausted = if bindings.state_aware {
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
            alpha_machine_key::<false>(value.operand_view(), bindings, next_binder)?,
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
        IntegerTerm::TruncatingQuotient(left, right) => AlphaIntegerNode::Binary {
            operator: IntegerTermBinaryOp::TruncatingQuotient,
            left: alpha_integer_node(left, bindings, memo, nodes, next_binder)?,
            right: alpha_integer_node(right, bindings, memo, nodes, next_binder)?,
        },
        IntegerTerm::TruncatingRemainder(left, right) => AlphaIntegerNode::Binary {
            operator: IntegerTermBinaryOp::TruncatingRemainder,
            left: alpha_integer_node(left, bindings, memo, nodes, next_binder)?,
            right: alpha_integer_node(right, bindings, memo, nodes, next_binder)?,
        },
        IntegerTerm::PureFunctionApplication(application) => {
            AlphaIntegerNode::PureFunctionApplication {
                name: application.name().to_owned(),
                arguments: application
                    .arguments()
                    .iter()
                    .map(|argument| {
                        alpha_pure_function_argument_key_with_bindings::<false>(
                            argument,
                            bindings,
                            next_binder,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?,
            }
        }
        IntegerTerm::AlgebraicMatch { .. } => return None,
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => AlphaIntegerNode::If {
            condition: Box::new(alpha_condition_key_with_bindings::<false>(
                condition,
                bindings,
                next_binder,
            )?),
            then_term: alpha_integer_node(then_term, bindings, memo, nodes, next_binder)?,
            else_term: alpha_integer_node(else_term, bindings, memo, nodes, next_binder)?,
        },
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            let alpha_index = match index {
                crate::kernel::IntegerRangeFoldIndex::Int32 { start, end }
                | crate::kernel::IntegerRangeFoldIndex::UInt64 { start, end } => {
                    let start = alpha_machine_key::<false>(
                        start.machine_operand().operand_view(),
                        bindings,
                        next_binder,
                    )?;
                    let end = alpha_machine_key::<false>(
                        end.machine_operand().operand_view(),
                        bindings,
                        next_binder,
                    )?;
                    // The kinds order their endpoints differently, so equal
                    // endpoint terms do not make equal folds.
                    if matches!(index, crate::kernel::IntegerRangeFoldIndex::Int32 { .. }) {
                        AlphaIntegerRangeIndex::Int32(start, end)
                    } else {
                        AlphaIntegerRangeIndex::UInt64(start, end)
                    }
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
    if bindings.state_aware && crate::kernel::is_load_variable(&variable) {
        // An unbound registered load is represented by its state-bearing
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
        let kind = crate::kernel::registered_load_kind_for_variable(&variable)?;
        let retained_state = AlphaStateKey::new(&memory);
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
        let load_id = intern_alpha_registered_load(&interner, retained_state, pointer, kind)?;
        Some((load_id, *next_binder))
    })();
    bindings.registered_load_stack.remove(&variable);
    let (load_id, next_after) = result?;
    bindings
        .registered_load_memo
        .insert(cache_key, (load_id.clone(), next_after));
    Some(load_id)
}

/// A pointer read keyed by the exact state and the alpha key of the
/// address it reads, as `alpha_registered_load_pointer_with_bindings` keys a
/// load variable: a binder inside the address renames, and two reads match
/// only when they read one state at alpha-equal addresses.
fn alpha_pointer_load_with_bindings<const ALLOW_LOADS: bool>(
    identity: crate::kernel::PointerLoadId,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaRegisteredLoadId> {
    let cache_key = (
        identity,
        bindings.integer_scope,
        bindings.bitvector_scope,
        *next_binder,
    );
    if let Some((load_id, next_after)) = bindings.pointer_load_memo.get(&cache_key) {
        *next_binder = *next_after;
        return Some(load_id.clone());
    }
    if !bindings.pointer_load_stack.insert(identity) {
        return None;
    }
    let result = (|| {
        let (memory, address) = crate::kernel::eval::registered_pointer_load(identity)?;
        let retained_state = AlphaStateKey::new(&memory);
        let address =
            alpha_pointer_key_with_bindings::<ALLOW_LOADS>(&address, bindings, next_binder)?;
        let interner = match bindings.load_interner.clone() {
            Some(interner) => interner,
            None => {
                let interner = alpha_registered_load_interner()?;
                bindings.load_interner = Some(interner.clone());
                interner
            }
        };
        alpha_work_checkpoint(bindings, 1)?;
        let load_id =
            intern_alpha_registered_load(&interner, retained_state, address, LoadKind::Bits64)?;
        Some((load_id, *next_binder))
    })();
    bindings.pointer_load_stack.remove(&identity);
    let (load_id, next_after) = result?;
    bindings
        .pointer_load_memo
        .insert(cache_key, (load_id.clone(), next_after));
    Some(load_id)
}

fn alpha_pointer_offset_key_with_bindings<const ALLOW_LOADS: bool>(
    offset: &PointerOffsetTerm,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaPointerOffsetKey> {
    alpha_work_checkpoint(bindings, 1)?;
    Some(Canonical::new(match offset {
        PointerOffsetTerm::Constant(value) => AlphaPointerOffsetNode::Constant(*value),
        PointerOffsetTerm::Variable(variable)
            if bindings.state_aware
                && crate::kernel::is_load_variable(variable)
                && !bindings.bitvector.contains_key(variable) =>
        {
            let load_id = alpha_registered_load_pointer_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                next_binder,
            )?;
            AlphaPointerOffsetNode::RegisteredLoad(load_id)
        }
        PointerOffsetTerm::Variable(variable) => {
            AlphaPointerOffsetNode::Variable(alpha_variable_key_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                &bindings.bitvector,
            )?)
        }
        PointerOffsetTerm::Add(left, right) => AlphaPointerOffsetNode::Add(
            alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(left, bindings, next_binder)?,
            alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(right, bindings, next_binder)?,
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            AlphaPointerOffsetNode::Int32Scaled {
                value: Canonical::new(alpha_machine_key::<ALLOW_LOADS>(
                    value.operand_view(),
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
        } => AlphaPointerOffsetNode::Int64Scaled {
            value: Canonical::new(alpha_machine_key::<ALLOW_LOADS>(
                value.operand_view(),
                bindings,
                next_binder,
            )?),
            byte_width: *byte_width,
            unsigned: *unsigned,
        },
    }))
}

fn alpha_pointer_block_key<const ALLOW_LOADS: bool>(
    block: &PointerBlock,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaPointerBlockKey> {
    Some(match block {
        // Keyed as the scalar and algebraic applications are, argument by
        // argument: a quantified fact is found only by its key, so a block
        // with none would hide every universal over a pointer result.
        PointerBlock::PureFunctionApplication(application) => {
            AlphaPointerBlockKey::PureFunctionApplication {
                name: application.name().to_string(),
                arguments: application
                    .arguments()
                    .iter()
                    .map(|argument| {
                        alpha_pure_function_argument_key_with_bindings::<ALLOW_LOADS>(
                            argument,
                            bindings,
                            next_binder,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?,
            }
        }
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
        PointerBlock::ExternalObject(variable) => {
            AlphaPointerBlockKey::ExternalObject(alpha_variable_key_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                &bindings.bitvector,
            )?)
        }
        PointerBlock::Symbolic(variable)
            if bindings.state_aware
                && crate::kernel::is_load_variable(variable)
                && !bindings.bitvector.contains_key(variable) =>
        {
            AlphaPointerBlockKey::RegisteredLoad(alpha_registered_load_pointer_with_bindings::<
                ALLOW_LOADS,
            >(*variable, bindings, next_binder)?)
        }
        PointerBlock::Symbolic(variable) => {
            AlphaPointerBlockKey::Symbolic(alpha_variable_key_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                &bindings.bitvector,
            )?)
        }
        PointerBlock::LoadedPointer(identity) if bindings.state_aware => {
            AlphaPointerBlockKey::LoadedRead(alpha_pointer_load_with_bindings::<ALLOW_LOADS>(
                *identity,
                bindings,
                next_binder,
            )?)
        }
        PointerBlock::LoadedPointer(identity) => AlphaPointerBlockKey::LoadedPointer(*identity),
        PointerBlock::Heap(identity) => AlphaPointerBlockKey::Heap(*identity),
        PointerBlock::Temporary(identity) => AlphaPointerBlockKey::Temporary(*identity),
    })
}

fn alpha_pointer_key_with_bindings<const ALLOW_LOADS: bool>(
    pointer: &Pointer,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaPointerKey> {
    alpha_work_checkpoint(bindings, 1)?;
    let block = alpha_pointer_block_key::<ALLOW_LOADS>(&pointer.block, bindings, next_binder)?;
    Some(AlphaPointerKey {
        block,
        offset: alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(
            &pointer.offset,
            bindings,
            next_binder,
        )?,
    })
}

fn alpha_program_value_key_with_bindings<const ALLOW_LOADS: bool>(
    value: &ProgramValue,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaProgramValueKey> {
    alpha_work_checkpoint(bindings, 1)?;
    Some(match value {
        ProgramValue::Void => AlphaProgramValueKey::Void,
        ProgramValue::Parameter(term) => {
            AlphaProgramValueKey::Parameter(Box::new(alpha_algebraic_key_with_bindings::<
                ALLOW_LOADS,
            >(term, bindings, next_binder)?))
        }
        ProgramValue::Pointer(pointer) => AlphaProgramValueKey::Pointer {
            program_type: pointer.program_type(),
            pointee_volatile: pointer.pointee_volatile(),
            pointee_constant: pointer.pointee_constant(),
            pointer: alpha_pointer_key_with_bindings::<ALLOW_LOADS>(
                pointer.pointer(),
                bindings,
                next_binder,
            )?,
            designation: alpha_pointer_key_with_bindings::<ALLOW_LOADS>(
                pointer.designation(),
                bindings,
                next_binder,
            )?,
            extent_known: pointer.extent_is_known(),
            opaque_extent: if pointer.extent_is_known() {
                None
            } else {
                match pointer.opaque_extent() {
                    Some(origin) => Some(alpha_pointer_key_with_bindings::<ALLOW_LOADS>(
                        origin,
                        bindings,
                        next_binder,
                    )?),
                    None => None,
                }
            },
            extent: match pointer.extent() {
                Some(extent) => Some((
                    alpha_pointer_key_with_bindings::<ALLOW_LOADS>(
                        &extent.start,
                        bindings,
                        next_binder,
                    )?,
                    alpha_machine_key::<ALLOW_LOADS>(
                        crate::kernel::MachineOperandView::Legacy(&extent.width),
                        bindings,
                        next_binder,
                    )?,
                )),
                None => None,
            },
        },
        other => {
            let (ty, term) = match other.numeric_value() {
                ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
                ProgramValue::Int128(term) => (ProgramType::Int128, term),
                ProgramValue::UInt128(term) => (ProgramType::UInt128, term),

                ProgramValue::Bool(term) => (ProgramType::Bool, term),
                ProgramValue::Int8(term) => (ProgramType::Int8, term),
                ProgramValue::Int16(term) => (ProgramType::Int16, term),
                ProgramValue::Int32(term) => (ProgramType::Int32, term),
                ProgramValue::UInt8(term) => (ProgramType::UInt8, term),
                ProgramValue::UInt16(term) => (ProgramType::UInt16, term),
                ProgramValue::UInt32(term) => (ProgramType::UInt32, term),
                ProgramValue::Int64(term) => (ProgramType::Int64, term),
                ProgramValue::UInt64(term) => (ProgramType::UInt64, term),
                ProgramValue::Float32(term) => (ProgramType::Float32, term),
                ProgramValue::Float64(term) => (ProgramType::Float64, term),
                ProgramValue::Void | ProgramValue::Pointer(_) | ProgramValue::Parameter(_) => {
                    unreachable!()
                }
            };
            AlphaProgramValueKey::Scalar(
                ty,
                alpha_machine_key::<ALLOW_LOADS>(
                    crate::kernel::MachineOperandView::Legacy(term),
                    bindings,
                    next_binder,
                )?,
            )
        }
    })
}

fn alpha_algebraic_key_with_bindings<const ALLOW_LOADS: bool>(
    term: &AlgebraicTerm,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaAlgebraicKey> {
    alpha_work_checkpoint(bindings, 1)?;
    Some(match &term.node {
        AlgebraicTermNode::Variable(variable) => AlphaAlgebraicKey::Variable(
            term.algebraic_type.clone(),
            bindings
                .algebraic
                .get(variable)
                .copied()
                .map_or(AlphaVariableKey::Free(*variable), AlphaVariableKey::Bound),
        ),
        AlgebraicTermNode::Constructor { variant, fields } => AlphaAlgebraicKey::Constructor {
            algebraic_type: term.algebraic_type.clone(),
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|field| {
                    Some(match field {
                        AlgebraicValue::Program(value) => AlphaAlgebraicValueKey::Program(
                            alpha_program_value_key_with_bindings::<ALLOW_LOADS>(
                                value,
                                bindings,
                                next_binder,
                            )?,
                        ),
                        AlgebraicValue::Integer(value) => AlphaAlgebraicValueKey::Integer(
                            alpha_integer_key_with_bindings(value, bindings, next_binder)?,
                        ),
                        AlgebraicValue::Algebraic(value) => {
                            AlphaAlgebraicValueKey::Algebraic(alpha_algebraic_key_with_bindings::<
                                ALLOW_LOADS,
                            >(
                                value, bindings, next_binder
                            )?)
                        }
                    })
                })
                .collect::<Option<Vec<_>>>()?,
        },
        AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
            AlphaAlgebraicKey::PureFunctionApplication {
                algebraic_type: term.algebraic_type.clone(),
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        alpha_pure_function_argument_key_with_bindings::<ALLOW_LOADS>(
                            argument,
                            bindings,
                            next_binder,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?,
            }
        }
        AlgebraicTermNode::MemoryLoad { memory, pointer } => AlphaAlgebraicKey::MemoryLoad {
            algebraic_type: term.algebraic_type.clone(),
            carrier: alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                &AlgebraicTermNode::memory_load_carrier(memory, pointer),
                bindings,
                next_binder,
            )?,
        },
        AlgebraicTermNode::Match { .. } | AlgebraicTermNode::If { .. } => {
            return None;
        }
    })
}

fn alpha_pure_function_argument_key_with_bindings<const ALLOW_LOADS: bool>(
    argument: &PureFunctionArgument,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaPureFunctionArgumentKey> {
    alpha_work_checkpoint(bindings, 1)?;
    Some(match argument {
        PureFunctionArgument::SharedMachine(value) => {
            AlphaPureFunctionArgumentKey::Value(AlphaProgramValueKey::Scalar(
                value.ty().program_type(),
                alpha_machine_key::<ALLOW_LOADS>(value.operand_view(), bindings, next_binder)?,
            ))
        }
        PureFunctionArgument::Value(value) => AlphaPureFunctionArgumentKey::Value(
            alpha_program_value_key_with_bindings::<ALLOW_LOADS>(value, bindings, next_binder)?,
        ),
        PureFunctionArgument::Integer(value) => AlphaPureFunctionArgumentKey::Integer(
            alpha_integer_key_with_bindings(value, bindings, next_binder)?,
        ),
        PureFunctionArgument::Algebraic(value) => AlphaPureFunctionArgumentKey::Algebraic(
            alpha_algebraic_key_with_bindings::<ALLOW_LOADS>(value, bindings, next_binder)?,
        ),
        PureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => AlphaPureFunctionArgumentKey::ArrayRef {
            memory: AlphaStateKey::new(&crate::kernel::intern_memory_ref(memory)),
            pointer: alpha_program_value_key_with_bindings::<ALLOW_LOADS>(
                pointer,
                bindings,
                next_binder,
            )?,
            element_type: *element_type,
        },
    })
}

fn alpha_bitvector_key_with_bindings<const ALLOW_LOADS: bool>(
    term: &MachineTerm,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    alpha_work_checkpoint(bindings, 1)?;
    // Load variables hide states too: their binders cannot be treated as
    // opaque free variables by the memory-free structural authority.
    if !ALLOW_LOADS
        && !bindings.state_aware
        && (matches!(term, MachineTerm::MemoryLoad(..))
            || matches!(term, MachineTerm::Variable(variable) if crate::kernel::is_load_variable(variable)))
    {
        return None;
    }
    Some(match term {
        MachineTerm::BoolCast { to, value } => AlphaBitvectorKey::BoolCast(
            *to,
            Box::new(alpha_condition_key_with_bindings::<ALLOW_LOADS>(
                value,
                bindings,
                next_binder,
            )?),
        ),
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            from: source,
            to: destination,
        } => AlphaBitvectorKey::MachineIntegerCast(
            *source,
            *destination,
            Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                value,
                bindings,
                next_binder,
            )?),
        ),

        native_constant!(_, _) => {
            AlphaBitvectorKey::MachineIntegerConstant(term.as_machine_constant()?)
        }

        // A `uint32` constant is its word's `Constant` (rule K1).
        bits32_constant!(value) => AlphaBitvectorKey::Constant(constant_u32(*value)),
        int64_constant!(value) => AlphaBitvectorKey::Int64Constant(constant_i64(*value)),
        uint64_constant!(value) => AlphaBitvectorKey::UInt64Constant(constant_u64(*value)),
        MachineTerm::Variable(variable) => {
            if let Some(ordinal) = bindings.bitvector.get(variable) {
                AlphaBitvectorKey::Variable(AlphaVariableKey::Bound(*ordinal))
            } else {
                match crate::kernel::is_load_variable(variable)
                    .then(|| crate::kernel::registered_load_for_variable(variable))
                    .flatten()
                {
                    Some(_) if bindings.state_aware => {
                        let load_id = alpha_registered_load_pointer_with_bindings::<ALLOW_LOADS>(
                            *variable,
                            bindings,
                            next_binder,
                        )?;
                        AlphaBitvectorKey::RegisteredLoad(load_id)
                    }
                    Some((_, pointer)) => AlphaBitvectorKey::Load(
                        Box::new(alpha_pointer_key_with_bindings::<ALLOW_LOADS>(
                            &pointer,
                            bindings,
                            next_binder,
                        )?),
                        crate::kernel::registered_load_kind_for_variable(variable)?,
                    ),
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
        unary_term!(Int32, BitwiseNot, body) => AlphaBitvectorKey::BitwiseNot(Box::new(
            alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder)?,
        )),
        MachineTerm::Unary {
            format,
            op,
            operand: body,
        } => AlphaBitvectorKey::Unary(
            *format,
            *op,
            Box::new(alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(
                body,
                bindings,
                next_binder,
            )?),
        ),
        MachineTerm::Float32Negate(body) => {
            AlphaBitvectorKey::Float32Negate(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(body, bindings, next_binder)?))
        }
        MachineTerm::Float64Negate(body) => {
            AlphaBitvectorKey::Float64Negate(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(body, bindings, next_binder)?))
        }
        MachineTerm::If {
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
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => fold_keys::machine_fold_key::<ALLOW_LOADS>(
            [
                start.as_ref(),
                end.as_ref(),
                initial.as_ref(),
                body.as_ref(),
            ]
            .map(crate::kernel::MachineOperandView::Legacy),
            *accumulator,
            *item,
            bindings,
            next_binder,
        )?,
        MachineTerm::PureFunctionApplication { name, arguments } => {
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
        MachineTerm::ClickFunctionApplication { name, arguments } => {
            AlphaBitvectorKey::ClickFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        alpha_pure_function_argument_key_with_bindings::<ALLOW_LOADS>(
                            argument,
                            bindings,
                            next_binder,
                        )
                    })
                    .collect::<Option<Vec<_>>>()?,
            }
        }
        MachineTerm::AlgebraicMatch { scrutinee, arms } => {
            match_keys::machine::<ALLOW_LOADS>(scrutinee, arms, bindings, next_binder)?
        }
        MachineTerm::MemoryLoad(memory, pointer, kind) if bindings.state_aware => {
            bindings.raw_state_load_seen = true;
            let retained_state = AlphaStateKey::new(memory);
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
                &interner,
                retained_state,
                pointer,
                *kind,
            )?)
        }
        MachineTerm::MemoryLoad(_, pointer, kind) => {
            bindings.raw_state_load_seen = true;
            AlphaBitvectorKey::Load(
                Box::new(alpha_pointer_key_with_bindings::<ALLOW_LOADS>(
                    pointer,
                    bindings,
                    next_binder,
                )?),
                *kind,
            )
        }
        MachineTerm::PointerAddress(pointer, _) => AlphaBitvectorKey::Address(Box::new(
            alpha_pointer_key_with_bindings::<ALLOW_LOADS>(pointer, bindings, next_binder)?,
        )),
        MachineTerm::IntegerToMachine { value, destination } => {
            AlphaBitvectorKey::IntegerToMachine(
                *destination,
                alpha_integer_key_with_bindings(value.as_ref(), bindings, next_binder)?,
            )
        }
        cast_term!(Int64From32, value) => {
            AlphaBitvectorKey::Int64From32(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(value, bindings, next_binder)?))
        }
        cast_term!(UInt64From32, value) => {
            AlphaBitvectorKey::UInt64From32(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(value, bindings, next_binder)?))
        }
        cast_term!(UInt32From64, value) => {
            AlphaBitvectorKey::UInt32From64(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(value, bindings, next_binder)?))
        }
        cast_term!(Int64FromUInt32, value) => {
            AlphaBitvectorKey::Int64FromUInt32(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(
                value, bindings, next_binder
            )?))
        }
        cast_term!(UInt64FromInt32, value) => {
            AlphaBitvectorKey::UInt64FromInt32(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(
                value, bindings, next_binder
            )?))
        }
        cast_term!(UInt64FromInt64, value) => {
            AlphaBitvectorKey::UInt64FromInt64(Box::new(alpha_bitvector_key_with_bindings::<
                ALLOW_LOADS,
            >(
                value, bindings, next_binder
            )?))
        }
        term => {
            let (operator, left, right) = term
                .as_binary()
                .expect("every other variant has its own arm");
            AlphaBitvectorKey::Binary(
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
            )
        }
    })
}

// The typed visitor is the production API.  Keep this narrow compatibility
// shim for the legacy unit tests that exercise the old one-map helper directly;
// both carrier maps start from the test's bindings, while the visitor itself
// still applies carrier-aware scope handling.
#[cfg(test)]
fn alpha_bitvector_key<const ALLOW_LOADS: bool>(
    term: &MachineTerm,
    bindings: &mut BTreeMap<Variable, usize>,
    next_binder: &mut usize,
) -> Option<AlphaBitvectorKey> {
    let mut typed = AlphaBindings {
        integer: bindings.clone(),
        bitvector: bindings.clone(),
        algebraic: bindings.clone(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        state_aware: false,
        raw_state_load_seen: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        pointer_load_stack: BTreeSet::new(),
        pointer_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    };
    let result = alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(term, &mut typed, next_binder);
    *bindings = typed.bitvector;
    result
}

// Alpha identity preserves the written relation and truth. In particular,
// `obtain` must not silently mirror a named existential's body.
fn alpha_comparison_view(
    condition: &ConditionTerm,
) -> Option<(
    crate::kernel::machine_integer::comparison::NativeComparisonView<'_>,
    u8,
)> {
    use crate::kernel::machine_integer::comparison::{
        comparison_view, structural_native_comparison_view,
    };
    let relation = match condition {
        ConditionTerm::Compare { relation, .. } => match relation {
            crate::kernel::CompareRelation::Equal => 0,
            crate::kernel::CompareRelation::LessThan => 2,
            crate::kernel::CompareRelation::LessEqual => 3,
            crate::kernel::CompareRelation::GreaterThan => 4,
            crate::kernel::CompareRelation::GreaterEqual => 5,
        },
        ConditionTerm::IntegerEqual(..) => 0,
        ConditionTerm::IntegerNotEqual(..) => 1,
        ConditionTerm::IntegerLessThan(..) => 2,
        ConditionTerm::IntegerLessEqual(..) => 3,
        ConditionTerm::IntegerGreaterThan(..) => 4,
        ConditionTerm::IntegerGreaterEqual(..) => 5,
        _ => return None,
    };
    let view = if matches!(condition, ConditionTerm::Compare { .. }) {
        comparison_view(condition, true)?
    } else {
        structural_native_comparison_view(condition, true)?
    };
    let mut view = view.widened().unwrap_or(view);
    if relation >= 4 {
        view.operands.swap(0, 1);
    }
    Some((view, relation))
}

fn alpha_comparison_key<const ALLOW_LOADS: bool>(
    view: crate::kernel::machine_integer::comparison::NativeComparisonView<'_>,
    relation: u8,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaConditionKey> {
    alpha_work_checkpoint(bindings, 1)?;
    let format = if relation <= 1 {
        match view.format {
            MachineIntegerType::UInt8 => MachineIntegerType::Int8,
            MachineIntegerType::UInt16 => MachineIntegerType::Int16,
            MachineIntegerType::UInt32 => MachineIntegerType::Int32,
            MachineIntegerType::UInt64 => MachineIntegerType::Int64,
            other => other,
        }
    } else {
        view.format
    };
    Some(AlphaConditionKey::MachineComparison(
        format,
        relation,
        alpha_machine_key::<ALLOW_LOADS>(view.operands[0].operand_view(), bindings, next_binder)?,
        alpha_machine_key::<ALLOW_LOADS>(view.operands[1].operand_view(), bindings, next_binder)?,
    ))
}

fn alpha_condition_key_with_bindings<const ALLOW_LOADS: bool>(
    condition: &ConditionTerm,
    bindings: &mut AlphaBindings,
    next_binder: &mut usize,
) -> Option<AlphaConditionKey> {
    if let Some((view, relation)) = alpha_comparison_view(condition) {
        return alpha_comparison_key::<ALLOW_LOADS>(view, relation, bindings, next_binder);
    }
    alpha_work_checkpoint(bindings, 1)?;
    // Keyed at the fact identity: a native 8- or 16-bit comparison and the
    // `int32` comparison of its widenings are one fact.
    if let Some((operator, left, right)) = condition.as_fact_comparison() {
        return Some(AlphaConditionKey::Binary(
            operator,
            alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(&left, bindings, next_binder)?,
            alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(&right, bindings, next_binder)?,
        ));
    }
    Some(match condition {
        ConditionTerm::Constant(value) => AlphaConditionKey::Constant(*value),
        ConditionTerm::Variable(variable) => {
            AlphaConditionKey::Variable(alpha_variable_key_with_bindings::<ALLOW_LOADS>(
                *variable,
                bindings,
                &bindings.bitvector,
            )?)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => AlphaConditionKey::PointerOffsetEqual(
            alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(left, bindings, next_binder)?,
            alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(right, bindings, next_binder)?,
        ),
        ConditionTerm::PointerValueEqual(left, right) => AlphaConditionKey::PointerValueEqual(
            Box::new(alpha_program_value_key_with_bindings::<ALLOW_LOADS>(
                &ProgramValue::Pointer((**left).clone()),
                bindings,
                next_binder,
            )?),
            Box::new(alpha_program_value_key_with_bindings::<ALLOW_LOADS>(
                &ProgramValue::Pointer((**right).clone()),
                bindings,
                next_binder,
            )?),
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
        ConditionTerm::AlgebraicEqual(left, right) => AlphaConditionKey::AlgebraicEqual(
            Box::new(alpha_algebraic_key_with_bindings::<ALLOW_LOADS>(
                left,
                bindings,
                next_binder,
            )?),
            Box::new(alpha_algebraic_key_with_bindings::<ALLOW_LOADS>(
                right,
                bindings,
                next_binder,
            )?),
        ),
        ConditionTerm::BoolApplication(application) => AlphaConditionKey::BoolApplication {
            name: application.name().to_owned(),
            arguments: application
                .arguments()
                .iter()
                .map(|argument| {
                    alpha_pure_function_argument_key_with_bindings::<ALLOW_LOADS>(
                        argument,
                        bindings,
                        next_binder,
                    )
                })
                .collect::<Option<Vec<_>>>()?,
        },
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => AlphaConditionKey::BoolIf(
            Box::new(alpha_condition_key_with_bindings::<ALLOW_LOADS>(
                condition,
                bindings,
                next_binder,
            )?),
            Box::new(alpha_condition_key_with_bindings::<ALLOW_LOADS>(
                then_condition,
                bindings,
                next_binder,
            )?),
            Box::new(alpha_condition_key_with_bindings::<ALLOW_LOADS>(
                else_condition,
                bindings,
                next_binder,
            )?),
        ),
        ConditionTerm::BoolEqual(left, right) => AlphaConditionKey::BoolEqual(
            Box::new(alpha_condition_key_with_bindings::<ALLOW_LOADS>(
                left,
                bindings,
                next_binder,
            )?),
            Box::new(alpha_condition_key_with_bindings::<ALLOW_LOADS>(
                right,
                bindings,
                next_binder,
            )?),
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
        algebraic: bindings.clone(),
        integer_scope: 0,
        bitvector_scope: 0,
        next_scope_id: 1,
        state_aware: false,
        raw_state_load_seen: false,
        registered_load_stack: BTreeSet::new(),
        registered_load_memo: HashMap::new(),
        pointer_load_stack: BTreeSet::new(),
        pointer_load_memo: HashMap::new(),
        load_interner: None,
        work_units: 0,
    };
    alpha_proposition_key_with_bindings::<ALLOW_LOADS>(proposition, &mut environment, next_binder)
}

/// Build the shared identity used for exact stated-requirement lookup and
/// Surface/kernel goal correspondence. MemoryState-aware load keys make a
/// registered load and its spelled load agree only when they name the same
/// memory version.
pub(crate) fn proposition_identity_key(
    proposition: &Proposition,
) -> Option<PropositionIdentityKey> {
    proposition_identity_key_with_raw_load_flag(proposition).map(|(key, _)| key)
}

/// Authority for alpha-renaming a proof-local algebraic binder in a captured
/// array-dependent fact. Array references carry opaque, exact states;
/// raw loads do not, because a quantified C variable can occur inside their
/// state contents. Those cases retain the memory-aware substitution rule.
pub(crate) fn quantified_algebraic_captured_array_identity_key(
    proposition: &Proposition,
) -> Option<PropositionIdentityKey> {
    if !matches!(
        proposition,
        Proposition::ForAll {
            sort: Sort::Algebraic(_),
            ..
        } | Proposition::Exists {
            sort: Sort::Algebraic(_),
            ..
        }
    ) {
        return None;
    }
    proposition_identity_key_with_raw_load_flag(proposition)
        .and_then(|(key, raw_load)| (!raw_load).then_some(key))
}

fn proposition_identity_key_with_raw_load_flag(
    proposition: &Proposition,
) -> Option<(PropositionIdentityKey, bool)> {
    if implication_chain_depth(proposition) > 128 {
        // The identity index is an optimization for exact fact lookup. Keep
        // very deep source-shaped chains in the authoritative fact set
        // without asking the alpha-key builder to recreate their topology.
        return None;
    }
    let mut environment = fold_keys::bindings();
    let key = alpha_proposition_key_with_bindings::<true>(proposition, &mut environment, &mut 0)?;
    Some((PropositionIdentityKey(key), environment.raw_state_load_seen))
}

/// Whether [`proposition_identity_key`] declines `proposition` by shape
/// alone, before any work: a source-shaped implication chain too deep for
/// the alpha-key builder.
pub(crate) fn proposition_identity_key_declines_shape(proposition: &Proposition) -> bool {
    implication_chain_depth(proposition) > 128
}

fn implication_chain_depth(proposition: &Proposition) -> usize {
    let mut depth = 0;
    let mut current = proposition;
    while let Proposition::Implies(_, body) = current {
        depth += 1;
        current = body;
    }
    depth
}

/// Compare propositions up to alpha-renaming of binders, while retaining
/// exact semantic identity for free variables, sorts, connectives, and memory
/// versions. Unsupported proposition forms return `false`.
pub(crate) fn propositions_are_alpha_equal(left: &Proposition, right: &Proposition) -> bool {
    if left == right {
        return true;
    }
    match (
        proposition_identity_key(left),
        proposition_identity_key(right),
    ) {
        (Some(left_key), Some(right_key)) => {
            left_key == right_key && predicate_states_share_storage(left, right)
        }
        // A pair of unsupported propositions must not compare equal merely
        // because both key walks declined to represent them. They are equal
        // when they are the same proposition up to the numbering of their
        // own binders, which one renumbering of each decides exactly.
        (None, None) => renumbered_binders(left, 0) == renumbered_binders(right, 0),
        _ => false,
    }
}

/// A variable range no lowering mints, for renumbering binders.
const RENUMBERED_BINDER_BASE: u64 = 9_600_000_000;

/// `proposition` with each quantifier's variable replaced, outermost first,
/// by the variable numbered for its depth, so two propositions that differ
/// only in how their binders are numbered become the same value. The walk is
/// over the connectives and quantifiers only, and each renaming is the
/// ordinary capture-avoiding substitution; a binder inside a term is left as
/// written, and such a pair then compares equal only when it is written the
/// same. Work is one substitution per binder.
fn renumbered_binders(proposition: &Proposition, depth: u64) -> Proposition {
    use crate::kernel::reasoning::substitute_bitvector_variable_in_proposition;
    match proposition {
        Proposition::And(left, right) => Proposition::And(
            Box::new(renumbered_binders(left, depth)),
            Box::new(renumbered_binders(right, depth)),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(renumbered_binders(left, depth)),
            Box::new(renumbered_binders(right, depth)),
        ),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(renumbered_binders(left, depth)),
            Box::new(renumbered_binders(right, depth)),
        ),
        Proposition::Not(body) => Proposition::Not(Box::new(renumbered_binders(body, depth))),
        Proposition::ForAll {
            var,
            sort,
            body,
            name,
        } => {
            let fresh = Variable(RENUMBERED_BINDER_BASE + depth);
            let body = substitute_bitvector_variable_in_proposition(
                body,
                *var,
                &MachineTerm::Variable(fresh),
            );
            Proposition::ForAll {
                var: fresh,
                sort: sort.clone(),
                body: Box::new(renumbered_binders(&body, depth + 1)),
                name: name.clone(),
            }
        }
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => {
            let fresh = Variable(RENUMBERED_BINDER_BASE + depth);
            let body = substitute_bitvector_variable_in_proposition(
                body,
                *var,
                &MachineTerm::Variable(fresh),
            );
            Proposition::Exists {
                name: name.clone(),
                var: fresh,
                sort: sort.clone(),
                body: Box::new(renumbered_binders(&body, depth + 1)),
            }
        }
        _ => proposition.clone(),
    }
}

#[cfg(test)]
mod proposition_identity_tests {
    use super::*;
    use crate::kernel::{Memory, ProgramValue};

    fn equal(left: MachineTerm, right: MachineTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            },
            true,
        )
    }

    fn forall(var: u64, body: Proposition) -> Proposition {
        Proposition::ForAll {
            name: Default::default(),
            var: Variable(var),
            sort: Sort::Bitvector32,
            body: Box::new(body),
        }
    }

    fn local_definedness_fact(memory: &Memory, variable: u64) -> Proposition {
        forall(
            variable,
            Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: Pointer {
                    block: "local:defined-array".into(),
                    offset: PointerOffsetTerm::scale_int32(
                        MachineTerm::Variable(Variable(variable)),
                        1,
                    ),
                },
                value_type: ProgramType::UInt8,
            },
        )
    }

    #[test]
    fn definedness_identity_keeps_object_and_lifetime_boundaries() {
        let _session = crate::kernel::VerificationSession::enter();
        let array = Pointer {
            block: "local:defined-array".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let other = Pointer {
            block: "local:defined-other".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = Memory::new()
            .with_uninitialized_block(array.block.clone(), 4)
            .with_uninitialized_block(other.block.clone(), 4)
            .store(array.clone(), crate::kernel::uint8(7u32));
        let key = proposition_identity_key(&local_definedness_fact(&before, 81_001)).unwrap();
        let disjoint = before
            .clone()
            .store(other, ProgramValue::Int32(9u32.into()));
        assert_eq!(
            Some(key.clone()),
            proposition_identity_key(&local_definedness_fact(&disjoint, 81_002))
        );
        let affected = before
            .clone()
            .store(array.clone(), crate::kernel::uint8(8u32));
        let retired = before.without_local_block(&array.block);
        let resized = before.clone().with_block(array.block.clone(), 8);
        let unknown_write = before.clone().store(
            Pointer::symbolic(Variable(81_003)),
            ProgramValue::Int32(1u32.into()),
        );
        for changed in [affected, retired, resized, unknown_write] {
            assert_ne!(
                Some(key.clone()),
                proposition_identity_key(&local_definedness_fact(&changed, 81_001))
            );
        }
        // An independently constructed unwritten object is not the old one.
        let uninitialized = Memory::new().with_uninitialized_block(array.block, 4);
        assert_ne!(
            Some(key),
            proposition_identity_key(&local_definedness_fact(&uninitialized, 81_001))
        );
    }

    /// Pure-function applications are keyed through typed arguments, so a
    /// separately lowered binder keeps its identity without erasing an array
    /// state or accidentally treating a free variable as bound.
    #[test]
    fn pure_function_applications_compare_equal_up_to_binder_numbering() {
        let application = |bound: u64| {
            equal(
                MachineTerm::ClickFunctionApplication {
                    name: "count".to_string(),
                    arguments: vec![crate::kernel::PureFunctionArgument::Value(
                        ProgramValue::Int32(MachineTerm::Variable(Variable(bound))),
                    )],
                },
                MachineTerm::constant(1),
            )
        };
        let left = forall(2_000_000, application(2_000_000));
        let right = forall(3_000_000, application(3_000_000));
        assert!(proposition_identity_key(&left).is_some());
        assert!(propositions_are_alpha_equal(&left, &right));
        let other = forall(3_000_000, application(7));
        assert!(!propositions_are_alpha_equal(&left, &other));
    }

    #[test]
    fn array_dependent_algebraic_existential_keeps_state_and_binding_identity() {
        let ty = crate::kernel::AlgebraicType::parameter("Fuel".into());
        let pointer = Pointer {
            block: "alpha-array".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = Memory::new().with_block("alpha-array", 8);
        let after = before.clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let make = |binder: u64, argument: u64, memory: Memory| Proposition::Exists {
            name: "fuel".into(),
            var: Variable(binder),
            sort: Sort::Algebraic(ty.clone()),
            body: Box::new(equal(
                MachineTerm::ClickFunctionApplication {
                    name: "walk".into(),
                    arguments: vec![
                        PureFunctionArgument::ArrayRef {
                            memory,
                            pointer: ProgramValue::pointer(pointer.clone()),
                            element_type: ProgramType::Int32,
                        },
                        PureFunctionArgument::Algebraic(AlgebraicTerm {
                            algebraic_type: ty.clone(),
                            node: AlgebraicTermNode::Variable(Variable(argument)),
                        }),
                    ],
                },
                MachineTerm::constant(0),
            )),
        };
        let original = make(2_000_000, 2_000_000, before.clone());
        assert!(quantified_algebraic_captured_array_identity_key(&original).is_some());
        assert!(propositions_are_alpha_equal(
            &original,
            &make(3_000_000, 3_000_000, before.clone())
        ));
        assert!(!propositions_are_alpha_equal(
            &original,
            &make(3_000_000, 3_000_000, after)
        ));
        assert!(!propositions_are_alpha_equal(
            &original,
            &make(3_000_000, 2_000_000, before)
        ));
        let raw_load = Proposition::Exists {
            name: "fuel".into(),
            var: Variable(2_000_000),
            sort: Sort::Algebraic(ty),
            body: Box::new(equal(
                MachineTerm::MemoryLoad(
                    Memory::new().with_block("alpha-array", 8).into(),
                    Box::new(pointer),
                    crate::kernel::LoadKind::Int32,
                ),
                MachineTerm::constant(0),
            )),
        };
        assert!(quantified_algebraic_captured_array_identity_key(&raw_load).is_none());
    }

    #[test]
    fn alpha_identity_is_capture_safe_and_name_blind() {
        let left = forall(
            1,
            Proposition::Exists {
                name: "left".into(),
                var: Variable(2),
                sort: Sort::Bitvector32,
                body: Box::new(Proposition::And(
                    Box::new(equal(
                        MachineTerm::Variable(Variable(1)),
                        MachineTerm::Variable(Variable(2)),
                    )),
                    Box::new(Proposition::Or(
                        Box::new(equal(
                            MachineTerm::Variable(Variable(2)),
                            MachineTerm::Variable(Variable(1_000)),
                        )),
                        Box::new(Proposition::Not(Box::new(equal(
                            MachineTerm::Variable(Variable(1)),
                            MachineTerm::constant(0),
                        )))),
                    )),
                )),
            },
        );
        let right = forall(
            11,
            Proposition::Exists {
                name: "right".into(),
                var: Variable(12),
                sort: Sort::Bitvector32,
                body: Box::new(Proposition::And(
                    Box::new(equal(
                        MachineTerm::Variable(Variable(11)),
                        MachineTerm::Variable(Variable(12)),
                    )),
                    Box::new(Proposition::Or(
                        Box::new(equal(
                            MachineTerm::Variable(Variable(12)),
                            MachineTerm::Variable(Variable(1_000)),
                        )),
                        Box::new(Proposition::Not(Box::new(equal(
                            MachineTerm::Variable(Variable(11)),
                            MachineTerm::constant(0),
                        )))),
                    )),
                )),
            },
        );
        assert!(propositions_are_alpha_equal(&left, &right));

        let changed_free = forall(
            11,
            Proposition::Exists {
                name: "right".into(),
                var: Variable(12),
                sort: Sort::Bitvector32,
                body: Box::new(equal(
                    MachineTerm::Variable(Variable(11)),
                    MachineTerm::Variable(Variable(1_001)),
                )),
            },
        );
        assert!(!propositions_are_alpha_equal(&left, &changed_free));
    }

    #[test]
    fn alpha_identity_rejects_sort_quantifier_and_nonbinder_changes() {
        let body = equal(MachineTerm::Variable(Variable(7)), MachineTerm::constant(3));
        let renamed = equal(MachineTerm::Variable(Variable(8)), MachineTerm::constant(3));
        assert!(propositions_are_alpha_equal(
            &forall(7, body.clone()),
            &forall(8, renamed)
        ));
        let integer = Proposition::ForAll {
            name: Default::default(),
            var: Variable(8),
            sort: Sort::Integer,
            body: Box::new(body.clone()),
        };
        assert!(!propositions_are_alpha_equal(
            &forall(8, body.clone()),
            &integer
        ));
        let exists = Proposition::Exists {
            name: "x".into(),
            var: Variable(8),
            sort: Sort::Bitvector32,
            body: Box::new(body.clone()),
        };
        assert!(!propositions_are_alpha_equal(
            &forall(8, body.clone()),
            &exists
        ));
        assert!(!propositions_are_alpha_equal(
            &forall(7, body),
            &forall(
                8,
                equal(MachineTerm::Variable(Variable(8)), MachineTerm::constant(4))
            ),
        ));
        assert!(!propositions_are_alpha_equal(
            &Proposition::Predicate {
                name: "unsupported-left".into(),
                arguments: Vec::new(),
            },
            &Proposition::Predicate {
                name: "unsupported-right".into(),
                arguments: Vec::new(),
            },
        ));
    }

    #[test]
    fn alpha_identity_tracks_shadowing_through_every_logical_connective() {
        let make = |outer: u64, inner: u64, witness: u64| {
            forall(
                outer,
                Proposition::And(
                    Box::new(equal(
                        MachineTerm::Variable(Variable(outer)),
                        MachineTerm::constant(0),
                    )),
                    Box::new(Proposition::Or(
                        Box::new(Proposition::Implies(
                            Box::new(Proposition::Exists {
                                name: "witness".into(),
                                var: Variable(inner),
                                sort: Sort::Bitvector32,
                                body: Box::new(Proposition::Not(Box::new(equal(
                                    MachineTerm::Variable(Variable(witness)),
                                    MachineTerm::constant(1),
                                )))),
                            }),
                            Box::new(equal(
                                MachineTerm::Variable(Variable(outer)),
                                MachineTerm::constant(2),
                            )),
                        )),
                        Box::new(Proposition::Not(Box::new(equal(
                            MachineTerm::Variable(Variable(outer)),
                            MachineTerm::constant(3),
                        )))),
                    )),
                ),
            )
        };
        assert!(propositions_are_alpha_equal(
            &make(1, 1, 1),
            &make(11, 11, 11)
        ));
        assert!(!propositions_are_alpha_equal(
            &make(1, 1, 1),
            &make(11, 12, 11)
        ));
    }

    #[test]
    fn alpha_identity_keeps_memory_versions_distinct() {
        let pointer = Pointer {
            block: "identity-version".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let left_memory = Memory::new().with_block("identity-version", 8);
        let right_memory = left_memory.clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(9)),
        );
        let left = Proposition::MemoryLoadable {
            memory: left_memory.clone(),
            base: pointer.clone(),
            bytes: MachineTerm::constant(1),
            wide: false,
        };
        let same = Proposition::MemoryLoadable {
            memory: left_memory,
            base: pointer.clone(),
            bytes: MachineTerm::constant(1),
            wide: false,
        };
        let changed = Proposition::MemoryLoadable {
            memory: right_memory,
            base: pointer,
            bytes: MachineTerm::constant(1),
            wide: false,
        };
        assert!(propositions_are_alpha_equal(&left, &same));
        assert!(!propositions_are_alpha_equal(&left, &changed));
    }

    #[test]
    fn alpha_identity_matches_registered_and_spelled_load_at_one_version() {
        let pointer = Pointer {
            block: "identity-registered-load".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = Memory::new().with_block("identity-registered-load", 8);
        let shared_memory = crate::kernel::intern_memory_ref(&memory);
        // The spelled side is a raw `MemoryLoad` term, which records no
        // width, so the named side must stand in the same width the
        // term-derived naming path assumes for it.
        let load = crate::kernel::load_variable_for_cell_with_origin(
            &shared_memory,
            &pointer,
            crate::kernel::LoadKind::Int32,
            crate::kernel::load_access_width_or_widest(&shared_memory, &pointer),
            &shared_memory,
        );
        let (load_memory, load_pointer) = crate::kernel::registered_load_for_variable(&load)
            .expect("registered load should retain its exact version");
        let spelled = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::MemoryLoad(
                    load_memory,
                    Box::new(load_pointer),
                    crate::kernel::LoadKind::Int32,
                )),
                right: Box::new(MachineTerm::constant(7)),
            },
            true,
        );
        let named = equal(MachineTerm::Variable(load), MachineTerm::constant(7));
        assert_eq!(
            proposition_identity_key(&spelled),
            proposition_identity_key(&named)
        );

        let changed_memory = memory.clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(9)),
        );
        let changed_shared = crate::kernel::intern_memory_ref(&changed_memory);
        let changed_load = crate::kernel::load_variable_for_cell_with_origin(
            &changed_shared,
            &pointer,
            crate::kernel::LoadKind::Int32,
            crate::kernel::load_access_width_or_widest(&changed_shared, &pointer),
            &changed_shared,
        );
        let (changed_memory, changed_pointer) =
            crate::kernel::registered_load_for_variable(&changed_load)
                .expect("changed registered load should retain its version");
        let changed_spelled = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::MemoryLoad(
                    changed_memory,
                    Box::new(changed_pointer),
                    crate::kernel::LoadKind::Int32,
                )),
                right: Box::new(MachineTerm::constant(7)),
            },
            true,
        );
        let changed_named = equal(
            MachineTerm::Variable(changed_load),
            MachineTerm::constant(7),
        );
        assert!(propositions_are_alpha_equal(
            &changed_spelled,
            &changed_named
        ));
        assert!(!propositions_are_alpha_equal(&spelled, &changed_named));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/fact_keys/proposition_identity_tests.rs");
    }
}

/// Exact alpha identity for fold equalities whose C payload contains loads.
/// Retained state handles make each load part of the key while the
/// pointer visitor canonicalizes fold-bound C variables by ordinal.
fn state_alpha_proposition_key(proposition: &Proposition) -> Option<(AlphaPropositionKey, usize)> {
    let mut environment = fold_keys::bindings();
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
        Proposition::Equal(Term::Bitvector32(left), Term::Bitvector32(right)) => {
            AlphaPropositionKey::EqualBitvector(
                alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(left, bindings, next_binder)?,
                alpha_bitvector_key_with_bindings::<ALLOW_LOADS>(right, bindings, next_binder)?,
            )
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            AlphaPropositionKey::EqualAlgebraic(
                alpha_algebraic_key_with_bindings::<ALLOW_LOADS>(left, bindings, next_binder)?,
                alpha_algebraic_key_with_bindings::<ALLOW_LOADS>(right, bindings, next_binder)?,
            )
        }
        Proposition::ConditionIs(condition, value) => AlphaPropositionKey::Condition(
            alpha_condition_key_with_bindings::<ALLOW_LOADS>(condition, bindings, next_binder)?,
            *value,
        ),
        Proposition::Predicate { name, arguments } => AlphaPropositionKey::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    alpha_work_checkpoint(bindings, 1)?;
                    Some(match argument {
                        Term::ExecutionState(state) => AlphaPredicateArgumentKey::StateMemory(
                            AlphaStateKey::new(&crate::kernel::intern_memory_ref(state.memory())),
                        ),
                        Term::Memory(memory) => AlphaPredicateArgumentKey::Memory(
                            AlphaStateKey::new(&crate::kernel::intern_memory_ref(memory)),
                        ),
                        Term::ProgramValue(value) => AlphaPredicateArgumentKey::Value(
                            alpha_program_value_key_with_bindings::<ALLOW_LOADS>(
                                value,
                                bindings,
                                next_binder,
                            )?,
                        ),
                        Term::Integer(value) => AlphaPredicateArgumentKey::Integer(
                            alpha_integer_key_with_bindings(value, bindings, next_binder)?,
                        ),
                        Term::Algebraic(value) => AlphaPredicateArgumentKey::Algebraic(
                            alpha_algebraic_key_with_bindings::<ALLOW_LOADS>(
                                value,
                                bindings,
                                next_binder,
                            )?,
                        ),
                        _ => return None,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
        },
        Proposition::MemoryReadDefined {
            memory,
            pointer,
            value_type,
        } => {
            if !ALLOW_LOADS {
                return None;
            }
            bindings.raw_state_load_seen = true;
            let prior_state_aware = bindings.state_aware;
            bindings.state_aware = true;
            let key = (|| -> Option<AlphaPropositionKey> {
                alpha_work_checkpoint(bindings, 1)?;
                let retained_state = crate::kernel::intern_memory_ref(memory);
                Some(AlphaPropositionKey::MemoryReadDefined {
                    memory: AlphaStateKey {
                        identity: retained_state.local_read_definedness_identity(pointer),
                        _state: retained_state.clone(),
                    },
                    pointer: alpha_pointer_key_with_bindings::<ALLOW_LOADS>(
                        pointer,
                        bindings,
                        next_binder,
                    )?,
                    value_type: *value_type,
                })
            })();
            bindings.state_aware = prior_state_aware;
            key?
        }
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => {
            if !ALLOW_LOADS {
                return None;
            }
            bindings.raw_state_load_seen = true;
            // A wide (64-bit extent) range keys like a narrow one, with its
            // width kind kept in the key so the two never alpha-match.
            // Loadability is an explicit checked premise, so its memory
            // state is part of the alpha identity.  Raw MemoryLoad terms
            // keep the existing state-blind selection behavior above;
            // only this atom temporarily enables the exact registered-load
            // representation for its selected pointer and width.
            let prior_state_aware = bindings.state_aware;
            bindings.state_aware = true;
            let key = (|| -> Option<AlphaPropositionKey> {
                alpha_work_checkpoint(bindings, 1)?;
                let retained_state = crate::kernel::intern_memory_ref(memory);
                Some(AlphaPropositionKey::MemoryLoadable {
                    memory: AlphaStateKey::new(&retained_state),
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
                    wide: *wide,
                })
            })();
            bindings.state_aware = prior_state_aware;
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
        Proposition::ForAll {
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
            } else if matches!(sort, Sort::Algebraic(_)) {
                let prior = bindings.algebraic.insert(*var, ordinal);
                let parent_scope = bindings.bitvector_scope;
                bindings.bitvector_scope = bindings.next_scope_id;
                bindings.next_scope_id = bindings.next_scope_id.checked_add(1)?;
                let body =
                    alpha_proposition_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder);
                bindings.bitvector_scope = parent_scope;
                if let Some(prior) = prior {
                    bindings.algebraic.insert(*var, prior);
                } else {
                    bindings.algebraic.remove(var);
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
            } else if matches!(sort, Sort::Algebraic(_)) {
                let prior = bindings.algebraic.insert(*var, ordinal);
                let parent_scope = bindings.bitvector_scope;
                bindings.bitvector_scope = bindings.next_scope_id;
                bindings.next_scope_id = bindings.next_scope_id.checked_add(1)?;
                let body =
                    alpha_proposition_key_with_bindings::<ALLOW_LOADS>(body, bindings, next_binder);
                bindings.bitvector_scope = parent_scope;
                if let Some(prior) = prior {
                    bindings.algebraic.insert(*var, prior);
                } else {
                    bindings.algebraic.remove(var);
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

/// The alpha-invariant bucket key of a quantified proposition, or of an
/// implication chain whose final consequent is quantified. Guarded
/// quantifiers such as `result == 1 implies forall (k) { ... }` are
/// independently lowered with fresh binders by a `have` and by the claim it
/// discharges; indexing the whole chain lets an explicit `known` find
/// the alpha-equivalent fact without a derivation search.
pub(crate) fn quantified_equivalence_index_key(
    proposition: &Proposition,
) -> Option<QuantifiedEquivalenceKey> {
    if !matches!(
        implication_chain_conclusion(proposition),
        Proposition::ForAll { .. } | Proposition::Exists { .. }
    ) {
        return None;
    }
    let comparison = super::term_rewrite::TermRewrite::arithmetic_comparison(proposition);
    if crate::instrumentation::deadline_exceeded() {
        return None;
    }
    alpha_proposition_key::<true>(
        comparison.as_ref().unwrap_or(proposition),
        &mut BTreeMap::new(),
        &mut 0,
    )
    .map(QuantifiedEquivalenceKey)
}

/// The final consequent of a (possibly empty) implication chain. The walk
/// visits only the chain's connective spine.
pub(crate) fn implication_chain_conclusion(mut proposition: &Proposition) -> &Proposition {
    while let Proposition::Implies(_, consequent) = proposition {
        proposition = consequent;
    }
    proposition
}

/// Compare only quantified propositions containing a loadability atom using
/// the checked, state-aware alpha representation. `None` means neither
/// proposition needs this path; `Some(false)` is a fail-closed mismatch,
/// including unsupported or exhausted key construction.
pub(crate) fn state_quantified_alpha_equivalent(
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
        // The display name is not part of proposition identity.  In
        // particular, a root existential that carries an exact loadability
        // payload must match after lowering chooses a different witness
        // spelling, just as it does in the shared alpha key.
        (Proposition::Exists { .. }, Proposition::Exists { .. }) => true,
        _ => false,
    };
    if !same_quantifier {
        return Some(false);
    }
    let Some((left_key, left_work)) = state_alpha_proposition_key(left) else {
        return Some(false);
    };
    let Some((right_key, right_work)) = state_alpha_proposition_key(right) else {
        return Some(false);
    };
    if crate::instrumentation::deadline_exceeded_with_work(left_work.saturating_add(right_work)) {
        return Some(false);
    }
    Some(left_key == right_key && predicate_states_share_storage(left, right))
}

/// The alpha key checks a predicate's state memory through exact interning.
/// Recheck its non-memory state before treating key equality as fact
/// equivalence. Shared persistent storage and independently built empty
/// environments compare in O(1); other constructions fail closed.
pub(crate) fn predicate_states_share_storage(left: &Proposition, right: &Proposition) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (left, right) {
            (Proposition::And(a, b), Proposition::And(c, d))
            | (Proposition::Or(a, b), Proposition::Or(c, d))
            | (Proposition::Implies(a, b), Proposition::Implies(c, d)) => {
                pending.push((a, c));
                pending.push((b, d));
            }
            (Proposition::ForAll { body: a, .. }, Proposition::ForAll { body: b, .. })
            | (Proposition::Exists { body: a, .. }, Proposition::Exists { body: b, .. })
            | (Proposition::Not(a), Proposition::Not(b)) => pending.push((a, b)),
            (
                Proposition::Predicate { arguments: a, .. },
                Proposition::Predicate { arguments: b, .. },
            ) => {
                if a.len() != b.len() {
                    return false;
                }
                for (a, b) in a.iter().zip(b) {
                    match (a, b) {
                        (Term::ExecutionState(a), Term::ExecutionState(b)) => {
                            if !a.shares_non_memory_storage_with(b) {
                                return false;
                            }
                        }
                        (Term::ExecutionState(_), _) | (_, Term::ExecutionState(_)) => {
                            return false;
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    true
}

fn checked_proposition_contains_memory_loadability(proposition: &Proposition) -> Result<bool, ()> {
    if crate::instrumentation::deadline_exceeded_with_work(1) {
        return Err(());
    }
    match proposition {
        Proposition::MemoryLoadable { .. } | Proposition::MemoryReadDefined { .. } => Ok(true),
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
/// state-blind selection key, this refuses all explicit and registered
/// loads; no state contents or memory relations are inspected.
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
    fn integer_function_applications_key_universals_up_to_their_binder() {
        let universal = |binder, function: &str| {
            let applied =
                IntegerTerm::PureFunctionApplication(crate::kernel::SharedPureApplication::intern(
                    function.into(),
                    vec![crate::kernel::PureFunctionArgument::Integer(
                        IntegerTerm::var(Variable(binder)).into(),
                    )],
                ));
            Proposition::ForAll {
                name: Default::default(),
                var: Variable(binder),
                sort: Sort::Integer,
                body: Box::new(Proposition::ConditionIs(
                    ConditionTerm::IntegerGreaterEqual(
                        applied.into(),
                        IntegerTerm::constant_i64(0).into(),
                    ),
                    true,
                )),
            }
        };
        let key = |proposition: &Proposition| {
            quantified_equivalence_index_key(proposition).expect("the universal has a key")
        };
        assert!(key(&universal(900, "sq")) == key(&universal(901, "sq")));
        assert!(key(&universal(900, "sq")) != key(&universal(900, "cube")));
    }

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
        let make = |variable, destination| MachineTerm::IntegerToMachine {
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

    #[test]
    fn wide_cast_alpha_keys_include_source_and_destination_and_rename_operands() {
        let make = |variable, source, destination| {
            MachineTerm::machine_integer_cast(source, destination, MachineTerm::Variable(variable))
        };
        let key = |variable, source, destination| {
            alpha_bitvector_key::<false>(
                &make(variable, source, destination),
                &mut BTreeMap::from([(variable, 0)]),
                &mut 1,
            )
            .unwrap()
        };
        let left = key(
            Variable(149_007),
            MachineIntegerType::Int64,
            MachineIntegerType::Int128,
        );
        assert_eq!(
            left,
            key(
                Variable(149_008),
                MachineIntegerType::Int64,
                MachineIntegerType::Int128
            )
        );
        assert_ne!(
            left,
            key(
                Variable(149_007),
                MachineIntegerType::UInt64,
                MachineIntegerType::Int128
            )
        );
        assert_ne!(
            left,
            key(
                Variable(149_007),
                MachineIntegerType::Int64,
                MachineIntegerType::UInt128
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
            start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
            end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(1)),
        };
        let body = |variable| {
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                MachineTerm::IntegerToMachine {
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

    fn shared_endpoint_fold(
        variable: Variable,
        format: MachineIntegerType,
        depth: usize,
    ) -> IntegerTerm {
        use crate::kernel::{KernelTerm, KernelTermImport, MachineBinaryOp};
        let payload: SharedIntegerTerm = IntegerTerm::var(variable).into();
        let mut root =
            KernelTerm::integer_to_machine(format, KernelTermImport::default().integer(&payload))
                .unwrap();
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let endpoint = SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(997999)))
            .with_shared_operand(root.with_machine_observation_type(MachineIntegerType::Int32))
            .unwrap();
        assert!(!endpoint.machine_operand().has_boxed_operand());
        let index = if format == MachineIntegerType::UInt64 {
            crate::kernel::IntegerRangeFoldIndex::UInt64 {
                start: endpoint.clone(),
                end: endpoint,
            }
        } else {
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: endpoint.clone(),
                end: endpoint,
            }
        };
        IntegerTerm::RangeFold {
            index,
            initial: IntegerTerm::constant_i64(0).into(),
            accumulator: Variable(997998),
            item: variable,
            body: IntegerTerm::var(Variable(997998)).into(),
        }
    }

    #[test]
    fn shared_endpoint_alpha_keys_preserve_conversions_and_outer_scope() {
        use crate::kernel::{KernelTermExport, VerificationSession};
        let _session = VerificationSession::enter();
        let a = Variable(997001);
        let b = Variable(997002);
        let mut keys = Vec::new();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let left = shared_endpoint_fold(a, format, 3);
            let right = shared_endpoint_fold(b, format, 3);
            let exports = KernelTermExport::machine_export_count();
            let key = alpha_integer_key(&left, &mut BTreeMap::from([(a, 0)])).unwrap();
            assert_eq!(
                key,
                alpha_integer_key(&right, &mut BTreeMap::from([(b, 0)])).unwrap()
            );
            assert_ne!(
                key,
                alpha_integer_key(&right, &mut BTreeMap::from([(a, 0)])).unwrap(),
                "endpoints stay in outer scope even when the item binder uses that name"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let mut written = MachineTerm::IntegerToMachine {
                destination: format,
                value: IntegerTerm::var(a).into(),
            };
            for _ in 0..3 {
                written = MachineTerm::Binary {
                    format,
                    op: crate::kernel::MachineBinaryOp::Add,
                    left: Box::new(written.clone()),
                    right: Box::new(written),
                };
            }
            let endpoint = SharedIntegerRangeEndpoint::intern(written);
            let mut native = left.clone();
            let IntegerTerm::RangeFold { index, .. } = &mut native else {
                unreachable!()
            };
            *index = if format == MachineIntegerType::UInt64 {
                crate::kernel::IntegerRangeFoldIndex::UInt64 {
                    start: endpoint.clone(),
                    end: endpoint,
                }
            } else {
                crate::kernel::IntegerRangeFoldIndex::Int32 {
                    start: endpoint.clone(),
                    end: endpoint,
                }
            };
            assert_eq!(
                key,
                alpha_integer_key(&native, &mut BTreeMap::from([(a, 0)])).unwrap()
            );
            keys.push(key);
        }
        assert_ne!(keys[0], keys[1], "index width remains part of identity");
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/fact_keys/integer_alpha_scaling_tests.rs");
    }
}

#[cfg(test)]
mod memory_state_alpha_tests {
    use super::*;
    use crate::kernel::{
        IntegerRangeFoldIndex, Memory, ProgramValue, SharedIntegerRangeEndpoint, SharedIntegerTerm,
        SharedMachineIntegerTerm,
    };

    fn int32_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
            end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(2)),
        }
    }

    fn fold_body(memory: &SharedMemory, item: Variable) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "retained_state-alpha".into(),
                    offset: PointerOffsetTerm::Variable(item),
                }),
                crate::kernel::LoadKind::Int32,
            ),
        ))
    }

    fn fold(memory: &SharedMemory, accumulator: Variable, item: Variable) -> IntegerTerm {
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

    fn registered_load_interner_live_states() -> BTreeSet<(u32, u32)> {
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
                .map(|record| record.retained_state.identity)
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
    fn state_alpha_fold_loads_require_exact_state_identity() {
        let pointer = Pointer {
            block: "retained_state-alpha".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before =
            crate::kernel::intern_memory(Memory::new().with_block("retained_state-alpha", 8));
        let after = crate::kernel::intern_memory(
            before
                .as_ref()
                .clone()
                .store(pointer, ProgramValue::Int32(MachineTerm::constant(7))),
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
        let changed_memory_state = integer_equality_alpha_key(&equality(fold(
            &after,
            Variable(311_000),
            Variable(311_001),
        )))
        .expect("changed-state fold should still have a key");

        assert_eq!(source, renamed);
        assert_ne!(source, changed_memory_state);
    }

    #[test]
    fn state_alpha_rejects_unknown_registered_loads() {
        let unknown_load = Variable((1 << 40) + 313);
        let memory =
            crate::kernel::intern_memory(Memory::new().with_block("retained_state-alpha", 8));
        let term = IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            Variable(312_000),
            Variable(312_001),
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                MachineTerm::MemoryLoad(
                    memory,
                    Box::new(Pointer {
                        block: "retained_state-alpha".into(),
                        offset: PointerOffsetTerm::Variable(unknown_load),
                    }),
                    crate::kernel::LoadKind::Int32,
                ),
            )),
        );

        assert!(integer_equality_alpha_key(&equality(term)).is_none());
    }

    #[test]
    fn state_alpha_registered_loads_keep_their_state_identity() {
        let pointer = Pointer {
            block: "retained_state-alpha".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before =
            crate::kernel::intern_memory(Memory::new().with_block("retained_state-alpha", 8));
        let after = crate::kernel::intern_memory(before.as_ref().clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(11)),
        ));
        let before_load = crate::kernel::load_variable_for_cell_with_origin(
            &before,
            &pointer,
            crate::kernel::LoadKind::Int32,
            4,
            &before,
        );
        let after_load = crate::kernel::load_variable_for_cell_with_origin(
            &after,
            &pointer,
            crate::kernel::LoadKind::Int32,
            4,
            &after,
        );

        let make = |load: Variable, accumulator: Variable, item: Variable| {
            IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    MachineTerm::Variable(load),
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
        .expect("registered load from another state should resolve to an exact key");

        assert_eq!(before_key, renamed_before_key);
        assert_ne!(before_key, after_key);
    }

    /// A pointer loaded from memory is its own block, named by its load
    /// variable, so `forall k { p[k] == 1 }` for a loaded `p` reads a cell
    /// whose block is a load. Renaming `k` renames the address inside the
    /// cell's load, and the key must follow it there as it does at an
    /// offset position; the load naming the block keeps its identity.
    #[test]
    fn state_alpha_renames_a_binder_under_a_loaded_pointer_block() {
        let block = "loaded-pointer-block-alpha";
        let memory = crate::kernel::intern_memory(Memory::new().with_block(block, 16));
        let field = |offset: i64| Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let loaded = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &field(0),
            crate::kernel::LoadKind::Int32,
            8,
            &memory,
        );
        let other = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &field(8),
            crate::kernel::LoadKind::Int32,
            8,
            &memory,
        );
        let every_element_is_one = |base: Variable, binder: Variable| {
            let element = Pointer {
                block: PointerBlock::Symbolic(base),
                offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(binder), 4),
            };
            let element_load = crate::kernel::load_variable_for_cell_with_origin(
                &memory,
                &element,
                crate::kernel::LoadKind::Int32,
                4,
                &memory,
            );
            Proposition::ForAll {
                name: Default::default(),
                var: binder,
                sort: Sort::ProgramInt32,
                body: Box::new(Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Variable(element_load)),
                        right: Box::new(MachineTerm::constant(1)),
                    },
                    true,
                )),
            }
        };

        let key = proposition_identity_key(&every_element_is_one(loaded, Variable(315_000)))
            .expect("a loaded pointer block should resolve to an exact key");
        let renamed = proposition_identity_key(&every_element_is_one(loaded, Variable(315_001)))
            .expect("a renamed binder should resolve to an exact key");
        let other_base = proposition_identity_key(&every_element_is_one(other, Variable(315_001)))
            .expect("another loaded pointer should resolve to an exact key");

        assert_eq!(key, renamed);
        assert_ne!(key, other_base);
    }

    #[test]
    fn state_alpha_explicit_and_registered_loads_share_nested_identity() {
        let block = "retained_state-alpha-equivalent-loads";
        let memory = crate::kernel::intern_memory(Memory::new().with_block(block, 64));
        let first_pointer = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let first_load = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &first_pointer,
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        );
        let nested_pointer = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Variable(first_load),
        };
        let nested_load = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &nested_pointer,
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        );
        // The load registry keeps the provenance-projected state used by
        // the minted variable.  Use those exact identities for the explicit
        // forms below; the original `memory` may project to a different DAG
        // version even though it names the same source cell.
        let (first_memory, first_registered_pointer) =
            crate::kernel::registered_load_for_variable(&first_load)
                .expect("first load should have a registry entry");
        let (nested_memory, nested_registered_pointer) =
            crate::kernel::registered_load_for_variable(&nested_load)
                .expect("nested load should have a registry entry");
        let fold_with_body = |body: MachineTerm| {
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
        let explicit_first: SharedIntegerTerm = fold_with_body(MachineTerm::MemoryLoad(
            first_memory,
            Box::new(first_registered_pointer),
            crate::kernel::LoadKind::Int32,
        ))
        .into();
        let registered_first: SharedIntegerTerm =
            fold_with_body(MachineTerm::Variable(first_load)).into();
        let explicit_nested: SharedIntegerTerm = fold_with_body(MachineTerm::MemoryLoad(
            nested_memory,
            Box::new(nested_registered_pointer),
            crate::kernel::LoadKind::Int32,
        ))
        .into();
        let registered_nested: SharedIntegerTerm =
            fold_with_body(MachineTerm::Variable(nested_load)).into();

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
    fn state_alpha_accepts_free_program_endpoints_and_body_values() {
        let start = Variable(319_000);
        let end = Variable(319_001);
        let payload = Variable(319_002);
        let make = |accumulator: Variable, item: Variable| {
            IntegerTerm::range_fold(
                IntegerRangeFoldIndex::Int32 {
                    start: SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(start)),
                    end: SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(end)),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    MachineTerm::Variable(payload),
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
    fn state_alpha_fold_comparison_uses_exact_state_identity() {
        let pointer = Pointer {
            block: "retained_state-alpha".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before =
            crate::kernel::intern_memory(Memory::new().with_block("retained_state-alpha", 8));
        let after = crate::kernel::intern_memory(
            before
                .as_ref()
                .clone()
                .store(pointer, ProgramValue::Int32(MachineTerm::constant(13))),
        );
        let make = |memory: &SharedMemory, accumulator: Variable, item: Variable| {
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
    fn state_alpha_nested_folds_canonicalize_load_pointers() {
        let pointer = Pointer {
            block: "retained_state-alpha".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before =
            crate::kernel::intern_memory(Memory::new().with_block("retained_state-alpha", 8));
        let after = crate::kernel::intern_memory(before.as_ref().clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(5)),
        ));
        let nested = |memory: &SharedMemory, accumulator: Variable, item: Variable| {
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
        let changed_memory_state = integer_equality_alpha_key(&equality(nested(
            &after,
            Variable(317_100),
            Variable(317_101),
        )))
        .expect("changed nested state should still have a key");

        assert_eq!(source, renamed);
        assert_ne!(source, changed_memory_state);
    }

    fn registered_load_chain(depth: usize) -> (SharedMemory, Variable) {
        let block = format!("retained_state-alpha-registry-{depth}");
        let memory = crate::kernel::intern_memory(Memory::new().with_block(block.clone(), 4096));
        let mut pointer = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut load = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        );
        for _ in 0..depth {
            pointer = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Variable(load),
            };
            load = crate::kernel::load_variable_for_cell_with_origin(
                &memory,
                &pointer,
                crate::kernel::LoadKind::Int32,
                4,
                &memory,
            );
        }
        (memory, load)
    }

    fn registered_load_branching_chain(depth: usize) -> (SharedMemory, Variable) {
        let block = format!("retained_state-alpha-registry-branch-{depth}");
        let memory = crate::kernel::intern_memory(Memory::new().with_block(block.clone(), 4096));
        let mut pointer = Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut load = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        );
        for _ in 0..depth {
            pointer = Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::Add(
                    Box::new(PointerOffsetTerm::Variable(load)),
                    Box::new(PointerOffsetTerm::Variable(load)),
                ),
            };
            load = crate::kernel::load_variable_for_cell_with_origin(
                &memory,
                &pointer,
                crate::kernel::LoadKind::Int32,
                4,
                &memory,
            );
        }
        (memory, load)
    }

    #[test]
    fn state_alpha_registered_load_dags_stop_at_the_active_budget() {
        let (_, load) = registered_load_chain(128);
        let term = IntegerTerm::range_fold(
            int32_index(),
            IntegerTerm::constant_i64(0),
            Variable(322_000),
            Variable(322_001),
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                MachineTerm::Variable(load),
            )),
        );
        let tactic = crate::instrumentation::TacticEvent {
            source_tactic_path: None,
            claim: "integer.state_alpha_budget".into(),
            tactic_index: 0,
            tactic_name: "state_alpha_budget".into(),
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
        assert!(key.is_none(), "budgeted state traversal must reject");
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
    fn state_alpha_drops_unreachable_registered_load_states() {
        let early_memory =
            crate::kernel::intern_memory(Memory::new().with_block("retained_state-alpha-early", 8));
        let early_term: SharedIntegerTerm =
            fold(&early_memory, Variable(324_000), Variable(324_001)).into();
        let early_key = integer_fold_alpha_key(&early_term).expect("early fold key");
        let early_identity = early_memory.arena_id();

        for index in 0..64u64 {
            let block = format!("retained_state-alpha-temporary-{index}");
            let memory = crate::kernel::intern_memory(Memory::new().with_block(block.clone(), 8));
            let term: SharedIntegerTerm = IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(324_100 + index * 2),
                Variable(324_101 + index * 2),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    MachineTerm::MemoryLoad(
                        memory,
                        Box::new(Pointer {
                            block: block.into(),
                            offset: PointerOffsetTerm::Constant(0),
                        }),
                        crate::kernel::LoadKind::Int32,
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
        assert!(registered_load_interner_live_states().contains(&early_identity));
        drop(early_key);

        let mut trigger_key = None;
        for index in 0..16u64 {
            let block = format!("retained_state-alpha-cleanup-trigger-{index}");
            let memory = crate::kernel::intern_memory(Memory::new().with_block(block.clone(), 8));
            let term: SharedIntegerTerm = IntegerTerm::range_fold(
                int32_index(),
                IntegerTerm::constant_i64(0),
                Variable(325_000 + index * 2),
                Variable(325_001 + index * 2),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    MachineTerm::MemoryLoad(
                        memory,
                        Box::new(Pointer {
                            block: block.into(),
                            offset: PointerOffsetTerm::Constant(0),
                        }),
                        crate::kernel::LoadKind::Int32,
                    ),
                )),
            )
            .into();
            trigger_key = Some(integer_fold_alpha_key(&term).expect("cleanup trigger key"));
        }
        assert!(!registered_load_interner_live_states().contains(&early_identity));
        drop(trigger_key);
        assert_eq!(registered_load_interner_stats(), (0, 0));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/fact_keys/memory_state_alpha_tests.rs");
    }
}

#[cfg(test)]
mod machine_quantifier_identity_tests {
    use super::*;

    #[test]
    fn quantified_machine_comparisons_share_native_and_integer_identity() {
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::LessEqual,
                CompareRelation::GreaterThan,
                CompareRelation::GreaterEqual,
            ] {
                for truth in [false, true] {
                    let native = ConditionTerm::Compare {
                        format,
                        relation,
                        left: Box::new(MachineTerm::Variable(Variable(981))),
                        right: Box::new(MachineTerm::Variable(Variable(982))),
                    };
                    let left =
                        IntegerTerm::from_machine(format, MachineTerm::Variable(Variable(981)))
                            .unwrap()
                            .into();
                    let right =
                        IntegerTerm::from_machine(format, MachineTerm::Variable(Variable(982)))
                            .unwrap()
                            .into();
                    let shared = match relation {
                        CompareRelation::Equal => ConditionTerm::IntegerEqual(left, right),
                        CompareRelation::LessThan => ConditionTerm::IntegerLessThan(left, right),
                        CompareRelation::LessEqual => ConditionTerm::IntegerLessEqual(left, right),
                        CompareRelation::GreaterThan => {
                            ConditionTerm::IntegerGreaterThan(left, right)
                        }
                        CompareRelation::GreaterEqual => {
                            ConditionTerm::IntegerGreaterEqual(left, right)
                        }
                    };
                    let quantified = |condition, truth| Proposition::ForAll {
                        var: Variable(981),
                        name: crate::kernel::BinderName::written("i"),
                        sort: Sort::ProgramInteger(format),
                        body: Box::new(Proposition::ConditionIs(condition, truth)),
                    };
                    assert!(
                        propositions_are_alpha_equal(
                            &quantified(native.clone(), truth),
                            &quantified(shared.clone(), truth)
                        ),
                        "{format:?} {relation:?} {truth}"
                    );
                    assert!(
                        !propositions_are_alpha_equal(
                            &quantified(native, !truth),
                            &quantified(shared, truth)
                        ),
                        "opposite polarity"
                    );
                }
            }
        }
    }

    #[test]
    fn wide_quantified_keys_rename_binders_without_erasing_width_or_high_bits() {
        let quantified = |variable, wide, bound| Proposition::Exists {
            name: "x".into(),
            var: Variable(variable),
            sort: Sort::ProgramInt64,
            body: Box::new(Proposition::ConditionIs(
                if wide {
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Variable(Variable(variable))),
                        right: Box::new(MachineTerm::int64_constant(bound)),
                    }
                } else {
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Variable(Variable(variable))),
                        right: Box::new(MachineTerm::constant(bound as u32)),
                    }
                },
                true,
            )),
        };
        let wide = quantified(1, true, 1i64 << 32);
        let renamed = quantified(2, true, 1i64 << 32);
        assert!(quantified_equivalence_index_key(&wide).is_some());
        assert!(propositions_are_alpha_equal(&wide, &renamed));
        assert!(!propositions_are_alpha_equal(
            &wide,
            &quantified(2, true, 0)
        ));
        assert!(!propositions_are_alpha_equal(
            &wide,
            &quantified(2, false, 1i64 << 32)
        ));
        let mut unsigned = renamed;
        let Proposition::Exists { sort, .. } = &mut unsigned else {
            unreachable!()
        };
        *sort = Sort::ProgramInteger(MachineIntegerType::UInt64);
        assert!(!propositions_are_alpha_equal(&wide, &unsigned));
    }
}

#[cfg(test)]
mod pointer_index_tests;

#[cfg(test)]
mod offset_condition_tests {
    use super::*;
    #[test]
    fn common_offset_condition_keys_match_native_and_retain_scale_and_signedness() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut keys = Vec::new();
        for width in [1, 8] {
            for unsigned in [false, true] {
                let source = ConditionTerm::PointerOffsetEqual(
                    Box::new(PointerOffsetTerm::Add(
                        Box::new(PointerOffsetTerm::Constant(0)),
                        Box::new(PointerOffsetTerm::scaled_int64_node(
                            MachineTerm::Variable(Variable(998600)),
                            width,
                            unsigned,
                        )),
                    )),
                    Box::new(PointerOffsetTerm::Constant(0)),
                );
                let root = crate::kernel::KernelTermImport::default().condition(&source);
                let expected = memory_erased_condition_key(&source);
                let actual = memory_erased_boolean_operand_key(
                    crate::kernel::BooleanOperandView::Shared(&root),
                );
                assert_eq!(actual, expected);
                assert!(!keys.contains(&actual));
                keys.push(actual);
            }
        }
    }
}

#[cfg(test)]
mod raw_pointer_condition_tests {
    use super::*;
    #[test]
    fn raw_pointer_condition_keys_match_native_and_keep_block_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut keys = Vec::new();
        for block in [
            PointerBlock::Symbolic(Variable(998610)),
            PointerBlock::ExternalObject(Variable(998610)),
            PointerBlock::FunctionSymbolic(Variable(998610)),
        ] {
            let source = ConditionTerm::PointerEqual(
                Box::new(Pointer {
                    block,
                    offset: PointerOffsetTerm::scaled_int64_node(
                        MachineTerm::Variable(Variable(998611)),
                        8,
                        true,
                    ),
                }),
                Box::new(Pointer::null()),
            );
            let root = crate::kernel::KernelTermImport::default().condition(&source);
            let actual =
                memory_erased_boolean_operand_key(crate::kernel::BooleanOperandView::Shared(&root));
            assert_eq!(actual, memory_erased_condition_key(&source));
            assert!(!keys.contains(&actual));
            keys.push(actual);
        }
    }
}

#[cfg(test)]
mod complete_pointer_condition_tests {
    use super::*;
    use crate::kernel::SubobjectExtent;
    #[test]
    fn complete_pointer_conditions_keep_state_domain_keys() {
        let _session = crate::kernel::VerificationSession::enter();
        let a = PointerValue::new(
            Pointer::symbolic(Variable(998620)),
            ProgramType::Int32Pointer,
        );
        let mut keys = Vec::new();
        for value in [
            a.clone(),
            a.clone().with_root_extent(),
            a.clone().with_extent(Some(SubobjectExtent {
                start: Pointer::null(),
                width: MachineTerm::constant(4),
            })),
        ] {
            let source = ConditionTerm::PointerValueEqual(Box::new(value), Box::new(a.clone()));
            let root = crate::kernel::KernelTermImport::default().condition(&source);
            let actual =
                memory_erased_boolean_operand_key(crate::kernel::BooleanOperandView::Shared(&root));
            assert_eq!(actual, memory_erased_condition_key(&source));
            assert!(!keys.contains(&actual));
            keys.push(actual);
        }
    }
}

#[cfg(test)]
mod overflow_condition_tests {
    use super::*;
    #[test]
    fn overflow_conditions_keep_exact_format_and_operation_keys() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut keys = Vec::new();
        for format in crate::kernel::machine_integer::FORMATS {
            for op in [
                crate::kernel::OverflowOperation::Add,
                crate::kernel::OverflowOperation::Subtract,
                crate::kernel::OverflowOperation::Multiply,
                crate::kernel::OverflowOperation::Divide,
                crate::kernel::OverflowOperation::ShiftLeft,
            ] {
                let source = ConditionTerm::Overflows {
                    format,
                    op,
                    left: Box::new(MachineTerm::Variable(Variable(998630))),
                    right: Box::new(MachineTerm::Variable(Variable(998631))),
                };
                let root = crate::kernel::KernelTermImport::default().condition(&source);
                let actual = memory_erased_boolean_operand_key(
                    crate::kernel::BooleanOperandView::Shared(&root),
                );
                assert_eq!(actual, memory_erased_condition_key(&source));
                assert!(!keys.contains(&actual));
                keys.push(actual);
            }
        }
    }
}
