// Staged common fold dependency reader; activated with fold producers.
mod float_conversions;
#[allow(dead_code)]
mod pointer_checks;
mod pointer_domains;
pub(in crate::kernel) use pointer_domains::{PointerDomain, PointerDomainSource};
#[allow(dead_code)]
mod retained_folds;
#[allow(dead_code)]
mod retained_matches;
use super::execution_facts::ContextFactKey;
use super::prelude::*;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    native_constant, uint32_constant, uint64_constant,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum SignedIntervalOperandKey {
    Written(MachineTerm),
    Shared(crate::kernel::KernelTerm),
}

#[cfg(test)]
thread_local! {
    /// Facts whose whole execution-variable ceiling was taken.
    static WHOLE_CEILING_FACTS: Cell<usize> = const { Cell::new(0) };
    static CONDITION_IMPLICATION_ANTECEDENT_CHECKS: Cell<usize> = const { Cell::new(0) };
    static MEMORY_SEPARATION_CANDIDATE_CHECKS: Cell<usize> = const { Cell::new(0) };
    static MEMORY_SEPARATION_RECURSIVE_CANDIDATE_CHECKS: Cell<usize> = const { Cell::new(0) };
    static BITVECTOR_EQUALITY_INDEX_FACT_VISITS: Cell<usize> = const { Cell::new(0) };
    static EXACT_CONSTANT_FACT_VISITS: Cell<usize> = const { Cell::new(0) };
    static CONDITION_FACT_VISITS: Cell<usize> = const { Cell::new(0) };
}

/// Counts one condition fact examined by a condition-fact query
/// (`has_condition_fact`, `exact_ordering_modulo_canonical_atoms`, the
/// symbolic pointer-equality hop), for the scaling regressions.
#[inline]
pub(in crate::kernel) fn count_condition_fact_visit() {
    #[cfg(test)]
    CONDITION_FACT_VISITS.with(|visits| visits.set(visits.get() + 1));
}
use std::cell::{Cell, RefCell};

pub(in crate::kernel) mod checked_order_bounds;
pub(in crate::kernel) mod checked_scalar_facts;
mod condition_reasoning;
pub(super) mod contradiction_endpoints;
pub(in crate::kernel) mod contradictions;
pub(in crate::kernel) mod exact_propagation;
pub(in crate::kernel) mod observation_comparisons;
pub(in crate::kernel) mod retained_order_bounds;
pub(in crate::kernel) mod shared_condition_variables;
pub(in crate::kernel) mod variable_chains;
use super::equality_graph::EqualityGraph;
use super::machine_integer::comparison::native_comparison_of_integer_observation;
#[cfg(test)]
use super::machine_integer::comparison::native_comparison_through_integer_operations;
#[cfg(test)]
use super::machine_integer::definedness::{
    definedness_of_integer_bound, integer_bounds_of_definedness,
};
#[cfg(test)]
use super::machine_integer::modular::wrapped_equality_of_integer_equality;
pub(in crate::kernel) use condition_reasoning::cancel_common_offset_addends;

pub(in crate::kernel) use condition_reasoning::narrowed_cast_identity;
pub(in crate::kernel) use condition_reasoning::order_view_at_format;

mod separation_classes;
pub(in crate::kernel) use separation_classes::SeparatedAddressIndex;

mod memory_reasoning;
pub(in crate::kernel) use memory_reasoning::additive_base_spellings;
pub(crate) use memory_reasoning::arm_frame_composite_definitions;
pub(in crate::kernel) use memory_reasoning::parameter_alias_bucket;
pub(in crate::kernel) use memory_reasoning::parameter_partition_root;
pub(in crate::kernel) use memory_reasoning::parameter_partition_variable;
pub(in crate::kernel) use memory_reasoning::read_candidate_byte_width;
pub(in crate::kernel) use memory_reasoning::signed_byte_sum_is_nonwrapping_views;
pub(in crate::kernel) use memory_reasoning::{
    frame_composite_definitions, owned_instances_naming_access_base,
};
pub(crate) mod proposition_reasoning;

pub(crate) use proposition_reasoning::finite_forall_goal_instances;

/// How a structural walk compares two load atoms. The walk itself is exact —
/// it only ever descends through matching constructors — so the whole
/// relation is only as strong as the load-atom rule plugged in here. Registered
/// names are offered before their raw origin states, allowing an explicit
/// named-load equality to supply authority without discarding those identities.
pub(in crate::kernel) type LoadAtomsMatch<'a> = &'a dyn Fn(&MachineTerm, &MachineTerm) -> bool;

pub(in crate::kernel) fn pointers_equal_with_load_atoms(
    left: &Address,
    right: &Address,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    address_bases_equal_with_load_atoms(&left.base, &right.base, loads_match)
        && offsets_equal_with_load_atoms(&left.offset, &right.offset, loads_match)
}

fn address_bases_equal_with_load_atoms(
    left: &AddressBase,
    right: &AddressBase,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    left == right
        || match (left, right) {
            (AddressBase::LoadedPointer(a), AddressBase::LoadedPointer(b)) => {
                let (Some((am, ap)), Some((bm, bp))) = (
                    crate::kernel::eval::registered_pointer_load(*a),
                    crate::kernel::eval::registered_pointer_load(*b),
                ) else {
                    return false;
                };
                loads_match(
                    &MachineTerm::MemoryLoad(ProgramPoint::at(&am), Box::new(ap), LoadKind::Bits64),
                    &MachineTerm::MemoryLoad(ProgramPoint::at(&bm), Box::new(bp), LoadKind::Bits64),
                )
            }
            (AddressBase::Symbolic(_), AddressBase::Symbolic(_)) => {
                let base = |block: &AddressBase| Address {
                    base: block.clone(),
                    offset: AddressOffset::Constant(0),
                };
                let (Some(first), Some(second)) = (
                    super::equality_graph::logical_pointer_read_term(&base(left)),
                    super::equality_graph::logical_pointer_read_term(&base(right)),
                ) else {
                    return false;
                };
                terms_equal_with_load_atoms(&first, &second, loads_match)
            }
            _ => false,
        }
}

fn offsets_equal_with_load_atoms(
    left: &AddressOffset,
    right: &AddressOffset,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    match (left, right) {
        (AddressOffset::Add(ll, lr), AddressOffset::Add(rl, rr)) => {
            offsets_equal_with_load_atoms(ll, rl, loads_match)
                && offsets_equal_with_load_atoms(lr, rr, loads_match)
        }
        (
            AddressOffset::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            AddressOffset::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && operands_equal_with_load_atoms(
                    MachineIntegerType::Int32,
                    left_value.operand_view(),
                    right_value.operand_view(),
                    loads_match,
                )
        }
        _ => left == right,
    }
}

fn terms_equal_with_load_atoms(
    left: &MachineTerm,
    right: &MachineTerm,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    // Original object classes guide decoding, not numeric address equality.
    // Compare the addresses through the same pointer/load-atom rule.
    if let (Some(left), Some(right)) = (left.address_pointer(), right.address_pointer()) {
        return pointers_equal_with_load_atoms(left, right, loads_match);
    }
    match (left, right) {
        (MachineTerm::MemoryLoad(_, _, _), MachineTerm::MemoryLoad(_, _, _)) => {
            loads_match(left, right)
        }
        (MachineTerm::Variable(variable), load @ MachineTerm::MemoryLoad(..)) => {
            crate::kernel::registered_load_origin_term_for_variable(variable)
                .is_some_and(|origin| loads_match(&origin, load))
        }
        (load @ MachineTerm::MemoryLoad(..), MachineTerm::Variable(variable)) => {
            crate::kernel::registered_load_origin_term_for_variable(variable)
                .is_some_and(|origin| loads_match(load, &origin))
        }
        // A registered load variable is a load atom too: the same cell named
        // at two states has two variables when the edge between them is
        // crossed only in context. Compare through the first-seen origin
        // states, which are DAG-connected; the canonical placeholder form
        // is unsuited to frame checks.
        (MachineTerm::Variable(a), MachineTerm::Variable(b))
            if a != b
                && crate::kernel::is_load_variable(a)
                && crate::kernel::is_load_variable(b) =>
        {
            if loads_match(left, right) {
                return true;
            }
            match (
                crate::kernel::registered_load_origin_term_for_variable(a),
                crate::kernel::registered_load_origin_term_for_variable(b),
            ) {
                (Some(left), Some(right)) => loads_match(&left, &right),
                _ => false,
            }
        }
        (
            MachineTerm::If {
                condition: left_condition,
                then_term: left_then,
                else_term: left_else,
            },
            MachineTerm::If {
                condition: right_condition,
                then_term: right_then,
                else_term: right_else,
            },
        ) => {
            conditions_equal_with_load_atoms(left_condition, right_condition, loads_match)
                && terms_equal_with_load_atoms(left_then, right_then, loads_match)
                && terms_equal_with_load_atoms(left_else, right_else, loads_match)
        }
        _ => {
            if let (Some((left_operator, ll, lr)), Some((right_operator, rl, rr))) =
                (left.as_binary(), right.as_binary())
            {
                left_operator == right_operator
                    && terms_equal_with_load_atoms(ll, rl, loads_match)
                    && terms_equal_with_load_atoms(lr, rr, loads_match)
            } else if let (Some((left_operator, left_value)), Some((right_operator, right_value))) =
                (left.as_unary(), right.as_unary())
            {
                left_operator == right_operator
                    && terms_equal_with_load_atoms(left_value, right_value, loads_match)
            } else {
                left == right
            }
        }
    }
}

/// Adapt only a selected leaf for the existing load-atom authority. Never
/// export a surrounding shared expression or open a read's state.
fn operand_load_leaf(operand: crate::kernel::MachineOperandView<'_>) -> Option<MachineTerm> {
    use crate::kernel::MachineOperandView as V;
    if let Some(variable) = operand.variable() {
        return Some(MachineTerm::Variable(*variable));
    }
    match operand {
        V::Shared(term) => term.machine_read_leaf().cloned(),
        V::Legacy(term @ MachineTerm::MemoryLoad(..)) => Some(term.clone()),
        _ => None,
    }
}

/// Compare retained arithmetic without exporting it. Shared/shared syntax
/// correspondence is cached independently of the load registry; every selected
/// read/variable leaf pair is checked against the caller's current load authority.
fn operands_equal_with_load_atoms(
    format: MachineIntegerType,
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    use crate::kernel::MachineOperandView as V;
    if let (V::Legacy(left), V::Legacy(right)) = (left, right) {
        return terms_equal_with_load_atoms(left, right, loads_match);
    }
    // Comparing two selected atoms needs no DAG correspondence summary.
    // Resolve registered load authority in this query, just as native atoms do.
    if let (Some(a), Some(b)) = (operand_load_leaf(left), operand_load_leaf(right)) {
        return terms_equal_with_load_atoms(&a, &b, loads_match);
    }
    if let (V::Shared(left), V::Shared(right)) = (left, right) {
        return crate::kernel::shared_condition_operand_leaf_pairs(format, left, right)
            .is_some_and(|pairs| {
                pairs.values().all(|(a, b)| {
                    if a.ty() == &crate::kernel::KernelType::Bool {
                        return boolean_operands_equal_with_load_atoms(
                            crate::kernel::BooleanOperandView::Shared(a),
                            crate::kernel::BooleanOperandView::Shared(b),
                            loads_match,
                        );
                    }
                    terms_equal_with_load_atoms(
                        &operand_load_leaf(V::Shared(a)).expect("selected leaf"),
                        &operand_load_leaf(V::Shared(b)).expect("selected leaf"),
                        loads_match,
                    )
                })
            });
    }
    let mut pending = vec![(format, left, right)];
    while let Some((format, left, right)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if let (V::Legacy(a), V::Legacy(b)) = (left, right) {
            if !terms_equal_with_load_atoms(a, b, loads_match) {
                return false;
            }
            continue;
        }
        if let (Some(a), Some(b)) = (operand_load_leaf(left), operand_load_leaf(right)) {
            if !terms_equal_with_load_atoms(&a, &b, loads_match) {
                return false;
            }
            continue;
        }
        if let (Some(a), Some(b)) = (left.literal(), right.literal()) {
            if !format
                .constant_from_term(&a)
                .zip(format.constant_from_term(&b))
                .is_some_and(|(a, b)| a.bits() == b.bits())
            {
                return false;
            }
            continue;
        }
        if let (Some((a, [al, ar])), Some((b, [bl, br]))) =
            (left.conditional_view(), right.conditional_view())
        {
            if !boolean_operands_equal_with_load_atoms(a, b, loads_match) {
                return false;
            }
            pending.extend([(format, al, bl), (format, ar, br)]);
            continue;
        }
        if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
            (left.binary(), right.binary())
        {
            if af != bf || ao != bo {
                return false;
            }
            pending.extend([(af, al, bl), (af, ar, br)]);
        } else if let (Some((af, ao, a)), Some((bf, bo, b))) = (left.unary(), right.unary()) {
            if af != bf || ao != bo {
                return false;
            }
            pending.push((af, a, b));
        } else if let (Some((ae, af, at, a)), Some((be, bf, bt, b))) = (left.cast(), right.cast()) {
            if ae != be || af != bf || at != bt {
                return false;
            }
            pending.push((af, a, b));
        } else {
            return false;
        }
    }
    true
}

fn comparison_views_equal_with_load_atoms(
    left: crate::kernel::machine_integer::comparison::StructuralComparisonView<'_>,
    right: crate::kernel::machine_integer::comparison::StructuralComparisonView<'_>,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    use crate::kernel::machine_integer::comparison::{FactOperand, fact_operand_identity};
    if left.relation != right.relation || left.negated != right.negated {
        return false;
    }
    let (lf, [ll, lr]) = fact_operand_identity(
        left.format,
        left.relation,
        left.operands.each_ref().map(|v| v.operand_view()),
    );
    let (rf, [rl, rr]) = fact_operand_identity(
        right.format,
        right.relation,
        right.operands.each_ref().map(|v| v.operand_view()),
    );
    if lf != rf {
        return false;
    }
    let same = |a, b| match (a, b) {
        (FactOperand::Term(a), FactOperand::Term(b)) => {
            operands_equal_with_load_atoms(lf, a, b, loads_match)
        }
        (FactOperand::Value(a), FactOperand::Value(b)) => a == b,
        (FactOperand::Value(value), FactOperand::Term(term))
        | (FactOperand::Term(term), FactOperand::Value(value)) => {
            term.literal()
                .and_then(|term| lf.constant_from_term(&term))
                .and_then(|constant| constant.to_i128())
                == Some(value)
        }
    };
    same(ll, rl) && same(lr, rr)
}

/// Common comparison operands retain their DAGs. Composite and opaque guards
/// keep the native reader's exact equality/refusal policy.
pub(in crate::kernel) fn boolean_operands_equal_with_load_atoms(
    left: crate::kernel::BooleanOperandView<'_>,
    right: crate::kernel::BooleanOperandView<'_>,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    use crate::kernel::machine_integer::comparison::structural_boolean_comparison_view;
    // Native conditions accept exact equality before asking load authority.
    // Reuse the immutable machine syntax memo so repeated growing guards do
    // not rewalk their shared arithmetic prefixes for this preliminary check.
    let exact = left.syntax_equal_by(right, |a, b| match (a, b) {
        (
            crate::kernel::MachineOperandView::Shared(a),
            crate::kernel::MachineOperandView::Shared(b),
        ) => crate::kernel::shared_machine_syntax_equal(a, b),
        _ => crate::kernel::machine_operand_syntax_cmp(a, b).is_eq(),
    });
    if exact {
        return true;
    }
    // Composite guards permit exact equality only. Do not recursively apply
    // permissive load authority to their children.
    if left.is_bool_value_form() || right.is_bool_value_form() {
        return false;
    }
    if let (Some(left), Some(right)) = (
        structural_boolean_comparison_view(left),
        structural_boolean_comparison_view(right),
    ) {
        return comparison_views_equal_with_load_atoms(left, right, loads_match);
    }
    match (left.overflow(), right.overflow()) {
        (Some((af, ao, a)), Some((bf, bo, b))) => {
            return af == bf
                && ao == bo
                && a.into_iter()
                    .zip(b)
                    .all(|(a, b)| operands_equal_with_load_atoms(af, a, b, loads_match));
        }
        (None, None) => {}
        _ => return false,
    }
    match (left.pointer_offsets(), right.pointer_offsets()) {
        (Some(a), Some(b)) => {
            return a.iter().zip(&b).all(|(a, b)| {
                pointer_checks::shared_offsets_equal_with_load_atoms(a, b, loads_match)
            });
        }
        (None, None) => {}
        _ => return false,
    }
    match (left.pointer_addresses(), right.pointer_addresses()) {
        (Some(a), Some(b)) => {
            return a.iter().zip(&b).all(|(a, b)| {
                pointer_checks::shared_addresses_equal_with_load_atoms(a, b, loads_match)
            });
        }
        (None, None) => {}
        _ => return false,
    }
    if left.pointer_values().is_some() || right.pointer_values().is_some() {
        return false;
    }
    conditions_equal_with_load_atoms(&left.native(), &right.native(), loads_match)
}

/// Exact structural condition equality with load atoms compared by
/// `loads_match`. Only matching constructors recurse and everything else
/// falls back to `==`, so two structurally different conditions never match
/// however permissive `loads_match` is.
pub(in crate::kernel) fn conditions_equal_with_load_atoms(
    left: &ConditionTerm,
    right: &ConditionTerm,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    if left == right {
        return true;
    }
    use crate::kernel::machine_integer::comparison::structural_comparison_view;
    if let (Some(left), Some(right)) = (
        structural_comparison_view(left),
        structural_comparison_view(right),
    ) {
        return comparison_views_equal_with_load_atoms(left, right, loads_match);
    }
    let terms = |ll, rl, lr, rr| {
        terms_equal_with_load_atoms(ll, rl, loads_match)
            && terms_equal_with_load_atoms(lr, rr, loads_match)
    };
    // Compared at the fact identity: a native 8- or 16-bit comparison and
    // the `int32` comparison of its widenings are one fact.
    if let (Some((left_operator, ll, lr)), Some((right_operator, rl, rr))) =
        (left.as_fact_comparison(), right.as_fact_comparison())
    {
        return left_operator == right_operator && terms(&ll, &rl, &lr, &rr);
    }
    match (left, right) {
        (ConditionTerm::AddressOffsetEqual(ll, lr), ConditionTerm::AddressOffsetEqual(rl, rr)) => {
            offsets_equal_with_load_atoms(ll, rl, loads_match)
                && offsets_equal_with_load_atoms(lr, rr, loads_match)
        }
        (ConditionTerm::AddressEqual(ll, lr), ConditionTerm::AddressEqual(rl, rr)) => {
            pointers_equal_with_load_atoms(ll, rl, loads_match)
                && pointers_equal_with_load_atoms(lr, rr, loads_match)
        }
        (ConditionTerm::AlgebraicEqual(ll, lr), ConditionTerm::AlgebraicEqual(rl, rr)) => {
            algebraic_terms_equal_with_load_atoms(ll, rl, loads_match)
                && algebraic_terms_equal_with_load_atoms(lr, rr, loads_match)
        }
        _ => false,
    }
}

/// Exact structural algebraic equality with each load of an abstract value
/// compared by `loads_match` on its scalar carrier: the value an address
/// holds is the same in two states when its bytes are.
fn algebraic_terms_equal_with_load_atoms(
    left: &AlgebraicTerm,
    right: &AlgebraicTerm,
    loads_match: LoadAtomsMatch<'_>,
) -> bool {
    if left == right {
        return true;
    }
    if left.algebraic_type != right.algebraic_type {
        return false;
    }
    let values = |left: &AlgebraicValue, right: &AlgebraicValue| match (left, right) {
        (
            AlgebraicValue::Program(ProgramValue::Parameter(left)),
            AlgebraicValue::Program(ProgramValue::Parameter(right)),
        ) => algebraic_terms_equal_with_load_atoms(left, right, loads_match),
        (AlgebraicValue::Algebraic(left), AlgebraicValue::Algebraic(right)) => {
            algebraic_terms_equal_with_load_atoms(left, right, loads_match)
        }
        _ => left == right,
    };
    match (&left.node, &right.node) {
        (
            AlgebraicTermNode::MemoryLoad {
                point: left_memory,
                pointer: left_pointer,
            },
            AlgebraicTermNode::MemoryLoad {
                point: right_memory,
                pointer: right_pointer,
            },
        ) => loads_match(
            &AlgebraicTermNode::memory_load_carrier(left_memory, left_pointer),
            &AlgebraicTermNode::memory_load_carrier(right_memory, right_pointer),
        ),
        (
            AlgebraicTermNode::Constructor {
                variant: left_variant,
                fields: left_fields,
            },
            AlgebraicTermNode::Constructor {
                variant: right_variant,
                fields: right_fields,
            },
        ) => {
            left_variant == right_variant
                && left_fields.len() == right_fields.len()
                && left_fields
                    .iter()
                    .zip(right_fields)
                    .all(|(left, right)| values(left, right))
        }
        _ => false,
    }
}

/// Compares two load atoms by their pointers alone, ignoring which memory
/// state each carries.
///
/// NOT sound as an equality on its own: two loads of one pointer in
/// different states hold different values whenever a write between the
/// states reached that pointer. It exists only as a cheap prefilter that
/// discards hopeless candidates before a proving comparison runs, and every
/// caller must decide the surviving pairs with a real check.
fn load_atoms_equal_ignoring_memories(left: &MachineTerm, right: &MachineTerm) -> bool {
    match (left, right) {
        (
            MachineTerm::MemoryLoad(_, left_pointer, left_kind),
            MachineTerm::MemoryLoad(_, right_pointer, right_kind),
        ) => {
            left_kind == right_kind && pointers_equal_ignoring_memories(left_pointer, right_pointer)
        }
        _ => left == right,
    }
}

/// Structural pointer equality that treats two loads of one location as
/// equal regardless of which memory state each form carries. Cheap:
/// no proving, no canonicalization.
pub(crate) fn pointers_equal_ignoring_memories(left: &Address, right: &Address) -> bool {
    pointers_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
}

/// Cheap, assumption-free necessary condition for
/// [`PureFactContext::conditions_equal_modulo_proven_states`]: same structure,
/// with load atoms compared by pointer only.
///
/// MemoryState-blind, so it is NOT an equivalence and must never decide fact
/// availability on its own — it only narrows the candidate set before the
/// proving comparison runs.
pub fn conditions_equal_ignoring_memories(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    if let (ConditionTerm::PointerEqual(a, b), ConditionTerm::PointerEqual(c, d)) = (left, right) {
        // Candidate selection only. The context's state bridge separately
        // compares both complete provenances before accepting this candidate.
        return a.program_type() == c.program_type()
            && b.program_type() == d.program_type()
            && pointers_equal_with_load_atoms(
                a.address(),
                c.address(),
                &load_atoms_equal_ignoring_memories,
            )
            && pointers_equal_with_load_atoms(
                b.address(),
                d.address(),
                &load_atoms_equal_ignoring_memories,
            );
    }
    conditions_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
}

/// The address of a memory range's first element, when the range provably
/// has one.
///
/// This anchor is what makes a separation say something about two pointers:
/// each range holds the element at its own anchor, so two separated ranges
/// cannot have the same anchor. A range that may be empty holds nothing and
/// states nothing about its anchor, so both endpoints must be constants that
/// settle that here, with no reasoning and no wrap-around question.
///
/// The anchor is computed the way any element address is, which also
/// normalizes a range that a composition re-expressed against another
/// object's base back to the address the pointer itself carries.
/// The kind and canonical sides a condition fact is filed under in
/// `condition_facts_by_sides`, or `None` for a kind
/// `PureFactContext::condition_matches` relates only to itself.
pub(in crate::kernel) fn condition_match_key(
    condition: &ConditionTerm,
) -> Option<crate::kernel::primitives::ConditionMatchKey> {
    use crate::kernel::primitives::ConditionMatchKey;
    // A native 8- or 16-bit comparison is keyed as the `int32` comparison
    // of its operands' widenings: the two are one fact (rule K8), so both
    // spellings share a bucket.
    if let Some(widened) =
        crate::kernel::machine_integer::comparison::narrow_comparison_as_int32(condition)
    {
        return match widened {
            ConditionTerm::Compare { .. } => condition_match_key(&widened),
            _ => None,
        };
    }
    let canonical = crate::kernel::eval::canonical_term;
    let ordered = |left: MachineTerm, right: MachineTerm| {
        if left <= right {
            (left, right)
        } else {
            (right, left)
        }
    };
    Some(match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } => {
            // A 32-bit equality compares bits at either signedness, through
            // σ (rule K6, as its fact identity reads it).
            let side = |term: &MachineTerm| canonical(term.sign_cast32_bits()).constant_word32();
            let (left, right) = ordered(side(left), side(right));
            ConditionMatchKey::Equal(left, right)
        }
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left,
            right,
        } => {
            let (left, right) = ordered(canonical(left), canonical(right));
            ConditionMatchKey::OverflowAdd(left, right)
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            let left = crate::kernel::eval::canonical_offset_term(left);
            let right = crate::kernel::eval::canonical_offset_term(right);
            if left <= right {
                ConditionMatchKey::OffsetEqual(left, right)
            } else {
                ConditionMatchKey::OffsetEqual(right, left)
            }
        }
        ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::LessThan,
            left: lower,
            right: upper,
        }
        | ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::GreaterThan,
            left: upper,
            right: lower,
        } => {
            if *format == MachineIntegerType::UInt32 {
                ConditionMatchKey::UnsignedOrder(true, canonical(lower), canonical(upper))
            } else {
                ConditionMatchKey::Order(true, canonical(lower), canonical(upper))
            }
        }
        ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::LessEqual,
            left: lower,
            right: upper,
        }
        | ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::GreaterEqual,
            left: upper,
            right: lower,
        } => {
            if *format == MachineIntegerType::UInt32 {
                ConditionMatchKey::UnsignedOrder(false, canonical(lower), canonical(upper))
            } else {
                ConditionMatchKey::Order(false, canonical(lower), canonical(upper))
            }
        }
        _ => return None,
    })
}

/// The key a `ResourceContains` fact is filed under: a memory range's base
/// block, or any other resource itself. `resource_contains_builtin` relates a
/// memory parent only to ranges over related addresses, and any other parent
/// only to itself.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::kernel) enum ResourceContainsKey {
    Block(AddressBase),
    Resource(Resource),
}

impl ResourceContainsKey {
    fn of(resource: &Resource) -> Self {
        match resource {
            Resource::Memory(range) => Self::Block(range.base().base.clone()),
            other => Self::Resource(other.clone()),
        }
    }
}

/// Whether a side of this condition is not an atom: see
/// `PureFactContext::open_condition_facts`.
fn condition_has_an_open_side(condition: &ConditionTerm) -> bool {
    let open = |term: MachineOperandView<'_>| {
        if term.word32_constant().is_some() {
            false
        } else if let Some(variable) = term.variable() {
            crate::kernel::eval::registered_load_for_variable(variable).is_some()
        } else {
            true
        }
    };
    let open_offset = |offset: &AddressOffset| match offset {
        AddressOffset::Constant(_) | AddressOffset::Variable(_) => false,
        AddressOffset::Int32Scaled { value, .. } => open(value.operand_view()),
        _ => true,
    };
    match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            left,
            right,
            ..
        }
        | ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left,
            right,
        } => open(MachineOperandView::Legacy(left)) || open(MachineOperandView::Legacy(right)),
        ConditionTerm::AddressOffsetEqual(left, right) => open_offset(left) || open_offset(right),
        _ => false,
    }
}

pub(in crate::kernel) fn memory_range_anchor(range: &MemoryRange) -> Option<AddressOffset> {
    let (Some(start), Some(end)) = (range.constant_start(), range.constant_end()) else {
        return None;
    };
    (range.element_width() > 0 && (start as i32) < (end as i32))
        .then(|| range.start_pointer().offset)
}

pub(super) fn resources_equal_ignoring_memories(left: &Resource, right: &Resource) -> bool {
    let values_match = |left: &ProgramValue, right: &ProgramValue| match (left, right) {
        (ProgramValue::Int32(left), ProgramValue::Int32(right))
        | (ProgramValue::UInt8(left), ProgramValue::UInt8(right)) => {
            terms_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
        }
        (ProgramValue::Int8(left), ProgramValue::Int8(right)) => {
            terms_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
        }
        (ProgramValue::Int16(left), ProgramValue::Int16(right))
        | (ProgramValue::UInt16(left), ProgramValue::UInt16(right)) => {
            terms_equal_with_load_atoms(left, right, &load_atoms_equal_ignoring_memories)
        }
        (ProgramValue::Pointer(left), ProgramValue::Pointer(right)) => {
            pointers_equal_ignoring_memories(left.address(), right.address())
        }
        _ => false,
    };
    match (left, right) {
        (Resource::Memory(left), Resource::Memory(right)) => {
            // The bounds are compared as terms, so ranges of one kind are
            // read alike; a wide range and an `Int32` one are not equal.
            let (left_start, left_end) = left.bound_terms();
            let (right_start, right_end) = right.bound_terms();
            left.element_width() == right.element_width()
                && left.wide_bounds().is_some() == right.wide_bounds().is_some()
                && terms_equal_with_load_atoms(
                    left_start,
                    right_start,
                    &load_atoms_equal_ignoring_memories,
                )
                && terms_equal_with_load_atoms(
                    left_end,
                    right_end,
                    &load_atoms_equal_ignoring_memories,
                )
                && pointers_equal_ignoring_memories(left.base(), right.base())
        }
        (
            Resource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            Resource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            Resource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            Resource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments.iter())
                    .all(|(left, right)| match (left, right) {
                        (
                            crate::kernel::ResourceFieldValue::Program(left),
                            crate::kernel::ResourceFieldValue::Program(right),
                        ) => values_match(left, right),
                        _ => left == right,
                    })
        }
        _ => false,
    }
}

/// The equality-graph vertex key for a term is its canonical form, so a raw
/// load term and the load variable for it share one vertex: the graph
/// joins equal terms by construction rather than by per-query bridging.
/// The memory state and cell a load term reads, for a raw load or a
/// registered load variable.
pub(in crate::kernel) fn load_state_and_pointer(
    term: &MachineTerm,
) -> Option<(SymbolicMemory, Address, LoadKind)> {
    let read = crate::kernel::eval::scalar_read_observation(
        crate::kernel::MachineOperandView::Legacy(term),
    )?;
    // Checking follows the recorded observation, even when structural version
    // selection retained an earlier representative state in the term.
    Some((
        (*read.origin.unwrap_or(read.memory)).clone(),
        read.pointer,
        read.kind,
    ))
}

pub(in crate::kernel) fn equality_graph_term_key(term: &MachineTerm) -> MachineTerm {
    crate::kernel::eval::canonical_term(term)
}

thread_local! {
    static SOLVE_FACT_CONDITIONS_IN_PROGRESS: RefCell<BTreeSet<(ConditionTerm, bool)>> =
        const { RefCell::new(BTreeSet::new()) };
    static CONDITION_DECISIONS_IN_PROGRESS: RefCell<BTreeSet<(Option<MachineIntegerType>, ConditionTerm)>> =
        const { RefCell::new(BTreeSet::new()) };
    static CONSULTED_PREMISES_STACK: RefCell<Vec<ConsultedPremisesFrame>> =
        const { RefCell::new(Vec::new()) };
    static RECORDING_CONSULTED_PREMISES: Cell<bool> = const { Cell::new(false) };
    static CAPTURING_IMPLICIT_CONSULTED_PREMISES: Cell<usize> = const { Cell::new(0) };
}

#[derive(Default)]
struct ConsultedPremisesFrame {
    premises: BTreeSet<Proposition>,
    queries: BTreeSet<Proposition>,
}

struct ConsultedPremisesCollectionGuard {
    active: bool,
}

impl ConsultedPremisesCollectionGuard {
    fn start() -> Self {
        CONSULTED_PREMISES_STACK.with(|stack| {
            stack.borrow_mut().push(ConsultedPremisesFrame::default());
        });
        Self { active: true }
    }

    fn finish(mut self) -> BTreeSet<Proposition> {
        let frame = CONSULTED_PREMISES_STACK.with(|stack| {
            stack
                .borrow_mut()
                .pop()
                .expect("consulted-premise collection stack")
        });
        self.active = false;
        frame.premises
    }
}

impl Drop for ConsultedPremisesCollectionGuard {
    fn drop(&mut self) {
        if self.active {
            CONSULTED_PREMISES_STACK.with(|stack| {
                stack.borrow_mut().pop();
            });
        }
    }
}

struct ConsultedPremisesRecordingGuard;

impl ConsultedPremisesRecordingGuard {
    fn start() -> Self {
        RECORDING_CONSULTED_PREMISES.with(|recording| recording.set(true));
        Self
    }
}

impl Drop for ConsultedPremisesRecordingGuard {
    fn drop(&mut self) {
        RECORDING_CONSULTED_PREMISES.with(|recording| recording.set(false));
    }
}

/// Collects the exact premises consumed by successful reasoning
/// during `body`. This is certificate-planning metadata only: it does not
/// enter execution paths, theorems, obligations, or fresh-name budgets.
pub(crate) fn collect_consulted_premises<T>(body: impl FnOnce() -> T) -> (T, Vec<Proposition>) {
    let guard = ConsultedPremisesCollectionGuard::start();
    let result = body();
    let premises = guard.finish();
    (result, premises.into_iter().collect())
}

pub(crate) fn record_consulted_premises(assumptions: &PureFactContext, proposition: &Proposition) {
    if RECORDING_CONSULTED_PREMISES.with(Cell::get) {
        return;
    }
    let should_derive = CONSULTED_PREMISES_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        let Some(active) = stack.last_mut() else {
            return false;
        };
        active.queries.insert(proposition.clone())
    });
    if !should_derive {
        return;
    }
    let _recording = ConsultedPremisesRecordingGuard::start();
    // Exact facts already identify their own certificate premise. The
    // general derivation builder used to fill in the rest, but it left the
    // kernel with the rest of the proposition search, and asking it for a
    // premise set would have conservatively attached its complete ambient
    // context anyway. Shared observations select their existing source from
    // the comparison or direct-bound index. A query with no selected exact
    // source contributes no premise here; certificate planning spells the step.
    let observed_source = match proposition {
        Proposition::ConditionIs(condition, truth)
            if !assumptions.contains_assumed_exact(proposition) =>
        {
            assumptions
                .observation_comparisons
                .source(condition.native_compat(), *truth)
                .cloned()
                .or_else(|| {
                    assumptions
                        .checked_order_bounds
                        .exact_observation_source(condition.native_compat(), *truth)
                })
        }
        _ => None,
    };
    let premises = if let Some(source) = observed_source {
        vec![source.clone()]
    } else if assumptions.proves_exact(proposition) {
        vec![proposition.clone()]
    } else {
        Vec::new()
    };
    CONSULTED_PREMISES_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        let Some(active) = stack.last_mut() else {
            return;
        };
        active.premises.extend(premises);
    });
}

pub(crate) fn capture_implicit_consulted_premises<T>(body: impl FnOnce() -> T) -> T {
    struct Guard;
    impl Drop for Guard {
        fn drop(&mut self) {
            CAPTURING_IMPLICIT_CONSULTED_PREMISES.with(|depth| depth.set(depth.get() - 1));
        }
    }

    CAPTURING_IMPLICIT_CONSULTED_PREMISES.with(|depth| depth.set(depth.get() + 1));
    let _guard = Guard;
    body()
}

pub(crate) fn record_implicit_consulted_premises(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) {
    if CAPTURING_IMPLICIT_CONSULTED_PREMISES.with(|depth| depth.get() != 0) {
        record_consulted_premises(assumptions, proposition);
    }
}

/// Whether implicit consulted premises are being captured on this thread:
/// a rule that would skip a question whose answer records consulted premises must
/// ask it while this holds.
pub(crate) fn implicit_consulted_premises_capturing() -> bool {
    CAPTURING_IMPLICIT_CONSULTED_PREMISES.with(|depth| depth.get() != 0)
}

/// True while any condition decision is in progress on this thread. Deep
/// reasoning helpers use this to avoid re-entering `decide` from inside a
/// decision, which would cycle through order-fact matching and memory-load
/// resolution.
pub(super) fn inside_condition_decision() -> bool {
    CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| !in_progress.borrow().is_empty())
}

type StatedIndexMap = crate::persistent::PersistentMap<
    crate::kernel::proof::PropositionIdentityKey,
    crate::persistent::PersistentSet<Proposition>,
>;

fn adjust_stated_index(
    index: &StatedIndexMap,
    key: crate::kernel::proof::PropositionIdentityKey,
    proposition: &Proposition,
) -> StatedIndexMap {
    let bucket = index.get(&key).cloned().unwrap_or_default();
    index.with_inserted(key, bucket.with_value(proposition.clone()))
}

/// A context's index of stated propositions by alpha/load identity key.
///
/// A context starts `Deferred`: each fact change appends one node to a
/// persistent chain without computing a key. A query builds every unbuilt
/// node from the nearest built ancestor down and records each node's index
/// on it, so a sibling sharing the chain later builds only its own suffix:
/// every fact change is keyed at most once however many contexts derive from
/// it, and never when no context asks. Contexts rebuilt from scratch
/// (`retain`/`clear`) are `Built` and maintained eagerly, as before.
#[derive(Clone)]
pub(crate) enum StatedPropositionIndex {
    Built(StatedIndexMap),
    Deferred(std::sync::Arc<DeferredStatedIndexNode>),
}

impl Default for StatedPropositionIndex {
    fn default() -> Self {
        Self::deferred_empty()
    }
}

impl std::fmt::Debug for StatedPropositionIndex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Built(index) => formatter.debug_tuple("Built").field(&index.len()).finish(),
            Self::Deferred(_) => formatter.write_str("Deferred"),
        }
    }
}

impl StatedPropositionIndex {
    fn deferred_empty() -> Self {
        Self::Deferred(std::sync::Arc::new(DeferredStatedIndexNode {
            parent: std::sync::Mutex::new(None),
            adjustment: None,
            built: std::sync::OnceLock::from(StatedIndexMap::default()),
        }))
    }

    #[cfg(test)]
    fn shares_storage_with(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Built(left), Self::Built(right)) => left.shares_root_with(right),
            (Self::Deferred(left), Self::Deferred(right)) => std::sync::Arc::ptr_eq(left, right),
            _ => false,
        }
    }
}

pub(crate) struct DeferredStatedIndexNode {
    /// The index this node's adjustment applies to, released once this node
    /// is built. The root has none and is built empty.
    parent: std::sync::Mutex<Option<std::sync::Arc<DeferredStatedIndexNode>>>,
    adjustment: Option<Proposition>,
    built: std::sync::OnceLock<StatedIndexMap>,
}

impl DeferredStatedIndexNode {
    fn parent(&self) -> Option<std::sync::Arc<DeferredStatedIndexNode>> {
        self.parent
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone()
    }

    /// Builds this node's index, and every unbuilt ancestor's, iteratively.
    /// `None` when a key walk stops at an exhausted budget: nothing partial is
    /// recorded.
    fn force(self: &std::sync::Arc<Self>) -> Option<&StatedIndexMap> {
        if let Some(index) = self.built.get() {
            return Some(index);
        }
        let mut unbuilt = vec![self.clone()];
        let mut index = loop {
            let parent = unbuilt
                .last()
                .and_then(|node| node.parent())
                .expect("an unbuilt node keeps its parent");
            match parent.built.get() {
                Some(index) => break index.clone(),
                None => unbuilt.push(parent),
            }
        };
        for node in unbuilt.iter().rev() {
            if let Some(proposition) = &node.adjustment {
                match crate::kernel::proof::proposition_identity_key(proposition) {
                    Some(key) => {
                        index = adjust_stated_index(&index, key, proposition);
                    }
                    None if crate::instrumentation::deadline_exceeded_with_work(0) => {
                        return None;
                    }
                    None => {}
                }
            }
            let _ = node.built.set(index.clone());
            // Built nodes answer from their own index; the history above them
            // is no longer needed by anything that holds this node.
            node.parent
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .take();
        }
        self.built.get()
    }
}

impl Drop for DeferredStatedIndexNode {
    /// Unlinks the chain iteratively, so dropping a context built from a
    /// long fact list cannot overflow the stack.
    fn drop(&mut self) {
        let mut parent = self
            .parent
            .get_mut()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take();
        while let Some(node) = parent {
            match std::sync::Arc::try_unwrap(node) {
                Ok(mut node) => {
                    parent = node
                        .parent
                        .get_mut()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .take();
                }
                Err(_) => break,
            }
        }
    }
}

thread_local! {
    // Fact-free queries share structural registration within a verification.
    // Never insert assumptions here; reset with all arena-dependent caches.
    static INTRINSIC_CONTEXT: RefCell<Option<std::rc::Rc<PureFactContext>>> =
        const { RefCell::new(None) };
    static INCOMPLETE_REASONING_EPOCH: Cell<u64> = const { Cell::new(0) };
    static DECIDE_MEMO: RefCell<std::collections::HashMap<(u64, ConditionTerm), Option<bool>>> =
        RefCell::new(std::collections::HashMap::new());
    static ASSUMPTIONS_MEMO_IDS: RefCell<std::collections::HashMap<PureFactContext, u64>> =
        RefCell::new(std::collections::HashMap::new());
    static NEXT_ASSUMPTIONS_MEMO_ID: Cell<u64> = const { Cell::new(0) };
    static LOGICAL_READ_MEMO_IDS: RefCell<std::collections::HashMap<(u64, u64), u64>> =
        RefCell::new(std::collections::HashMap::new());
    static TRANSPORT_EQUAL_MEMO: RefCell<
        std::collections::HashMap<(u64, checked_scalar_facts::ScalarOperandKey, checked_scalar_facts::ScalarOperandKey), bool>,
    > = RefCell::new(std::collections::HashMap::new());
    static CONSTANT_NORMALIZATION_MEMO: RefCell<
        std::collections::HashMap<(u64, MachineTerm), Option<i64>>,
    > = RefCell::new(std::collections::HashMap::new());
    static SIGNED_INTERVAL_MEMO: RefCell<
        std::collections::HashMap<(u64, SignedIntervalOperandKey), Option<(i64, i64)>>,
    > = RefCell::new(std::collections::HashMap::new());
    /// Keyed by `atomic_derivation_memo_key`: the premises, whether the
    /// query is for `solve`, and the DAG modes the derivation reads.
    static ATOMIC_DERIVATION_MEMO: RefCell<
        std::collections::HashMap<
            (u64, bool, bool, bool),
            std::collections::HashMap<Proposition, Option<AtomicPropositionDerivationEvidence>>,
        >,
    > = RefCell::new(std::collections::HashMap::new());
}

/// Empties this module's memo tables at a verification boundary (ids keep
/// counting, so a later entry cannot alias an old id).
pub(crate) fn clear_assumption_memos() {
    crate::kernel::equality_graph::EqualityGraph::clear_constant_query_memos();
    OPERAND_FINGERPRINTS.with(|memo| memo.borrow_mut().clear());
    INTRINSIC_CONTEXT.with(|context| *context.borrow_mut() = None);
    DECIDE_MEMO.with(|memo| memo.borrow_mut().clear());
    ASSUMPTIONS_MEMO_IDS.with(|ids| ids.borrow_mut().clear());
    LOGICAL_READ_MEMO_IDS.with(|ids| ids.borrow_mut().clear());
    TRANSPORT_EQUAL_MEMO.with(|memo| memo.borrow_mut().clear());
    CONSTANT_NORMALIZATION_MEMO.with(|memo| memo.borrow_mut().clear());
    SIGNED_INTERVAL_MEMO.with(|memo| memo.borrow_mut().clear());
    ATOMIC_DERIVATION_MEMO.with(|memo| memo.borrow_mut().clear());
}

// The memo tables are bounded so a long verification cannot grow them without
// limit. Ids are drawn from a never-reset counter, so clearing the intern
// table cannot alias an old id to different contents.
const ASSUMPTIONS_MEMO_ID_LIMIT: usize = 20_000;
const DECIDE_MEMO_LIMIT: usize = 500_000;
const SIGNED_INTERVAL_MEMO_LIMIT: usize = 100_000;

/// Content-derived memo identity: equal fact sets share an id, and any
/// in-place mutation changes the contents and therefore the id, so a decision
/// memoized under an id can never be checked against different facts.
fn assumptions_memo_id(assumptions: &PureFactContext) -> u64 {
    ASSUMPTIONS_MEMO_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        if let Some(id) = ids.get(assumptions) {
            return *id;
        }
        if ids.len() >= ASSUMPTIONS_MEMO_ID_LIMIT {
            ids.clear();
        }
        let id = NEXT_ASSUMPTIONS_MEMO_ID.with(|next| {
            let id = next.get();
            next.set(id + 1);
            id
        });
        // This table owns identity keys, never contexts used for planning.
        // Do not keep dependency indexes from every transient restricted
        // context alive until the next verification boundary. They are
        // excluded from PureFactContext equality and hashing.
        let mut key = assumptions.clone();
        key.equality_graph = assumptions.equality_graph.identity_only();
        key.atomic_connection_facts = crate::persistent::PersistentMap::default();
        key.atomic_ground_facts = crate::kernel::fact_collections::ScanSet::default();
        key.atomic_quantified_facts = crate::kernel::fact_collections::ScanSet::default();
        key.explicit_memory_boundaries = Default::default();
        key.universals_by_conclusion = crate::persistent::PersistentMap::default();
        key.universal_equality_sources = Default::default();
        key.shared_condition_variables = Default::default();
        key.condition_facts_by_variable = crate::persistent::PersistentMap::default();
        key.state_condition_variable_base = crate::persistent::PersistentMap::default();
        key.state_condition_variable_changes = crate::persistent::PersistentMap::default();
        key.state_condition_variables = std::sync::Arc::new(std::sync::OnceLock::new());
        key.memory_load_condition_facts = crate::persistent::PersistentMap::default();
        // Lazy query caches may be populated *after* this clone is interned.
        // The identity table must not own their shared OnceLocks either.
        key.memory_loadable_shape_facts = crate::persistent::PersistentMap::default();
        ids.insert(key, id);
        id
    })
}

#[cfg(test)]
mod planning_index_memo_lifetime_tests {
    use super::*;

    #[test]
    fn memo_identity_does_not_retain_transient_indexes() {
        clear_assumption_memos();
        for size in [8u64, 16, 32, 64] {
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_proposition(Proposition::condition_is(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Variable(Variable(size * 1000 + index))),
                        right: Box::new(MachineTerm::constant(7)),
                    },
                    true,
                ));
            }
            let cache = std::sync::Arc::downgrade(&context.state_condition_variables);
            let id = assumptions_memo_id(&context);
            // The identity key exists before the live context populates a
            // shared cache; dropping only already-built data is insufficient.
            assert_eq!(assumptions_memo_id(&context), id);
            let copy = context.clone();
            assert_eq!(assumptions_memo_id(&copy), id);
            drop(copy);
            drop(context);
            assert!(
                cache.upgrade().is_none(),
                "size {size}: memo identity retained planning state"
            );
        }
        clear_assumption_memos();
    }
}

/// The content-derived memo id of a fact set, never salted by a search
/// attempt: the identity [`crate::kernel::reasoning::with_closure_failure_memo`]
/// keys its negative answers by, so one closure's candidates share them.
pub(crate) fn unsalted_assumptions_memo_id(assumptions: &PureFactContext) -> u64 {
    memo_id_with_logical_reads(assumptions_memo_id(assumptions), assumptions)
}

/// Term registration or a checked read equality can turn an earlier miss into
/// a hit without adding a proposition. Namespace reasoning memos by their
/// generation; never scan or flush the ambient fact set.
fn memo_id_with_logical_reads(base: u64, assumptions: &PureFactContext) -> u64 {
    let generation = assumptions.equality_graph.logical_read_generation();
    if generation == 0 {
        return base;
    }
    LOGICAL_READ_MEMO_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        if let Some(id) = ids.get(&(base, generation)) {
            return *id;
        }
        if ids.len() >= ASSUMPTIONS_MEMO_ID_LIMIT {
            ids.clear();
        }
        let id = NEXT_ASSUMPTIONS_MEMO_ID.with(|next| {
            let id = next.get();
            next.set(id + 1);
            id
        });
        ids.insert((base, generation), id);
        id
    })
}

/// Memo identity for the DAG-walk memo tables in api.rs: the ambient scope's
/// id when one is live (no hashing), the content-derived id otherwise.
pub(super) fn dag_memo_assumptions_id(assumptions: &PureFactContext) -> u64 {
    ambient_assumptions_memo_id(assumptions)
        .unwrap_or_else(|| apply_attempt_salt(unsalted_assumptions_memo_id(assumptions)))
}

thread_local! {
    static ASSUMPTIONS_ID_SCOPES: RefCell<Vec<(usize, u64)>> = const { RefCell::new(Vec::new()) };
}

/// Resolves the memo id for a fact set that is borrowed for the duration of
/// the returned guard, skipping the content hash when an enclosing scope
/// already resolved the same object.
///
/// The address comparison is sound because every recorded scope belongs to a
/// live borrow further up the stack: while such a borrow is alive its object
/// cannot be dropped, so an equal address is the same object with the same
/// contents.
pub(crate) struct PureFactContextIdScope {
    id: u64,
    pushed: bool,
}

impl PureFactContextIdScope {
    pub(crate) fn enter(assumptions: &PureFactContext) -> Self {
        if let Some(id) = ambient_assumptions_memo_id(assumptions) {
            return Self { id, pushed: false };
        }
        let address = assumptions as *const PureFactContext as usize;
        let id = assumptions_memo_id(assumptions);
        ASSUMPTIONS_ID_SCOPES.with(|scopes| scopes.borrow_mut().push((address, id)));
        Self {
            id: apply_attempt_salt(memo_id_with_logical_reads(id, assumptions)),
            pushed: true,
        }
    }
}

/// The memo id for this fact set if an enclosing [`PureFactContextIdScope`]
/// already resolved this same object, with no content hashing. Interior
/// reasoning helpers use this so only designated entry points ever pay the
/// hash; outside any scope they simply run unmemoized, as before memoization
/// existed.
pub(super) fn ambient_assumptions_memo_id(assumptions: &PureFactContext) -> Option<u64> {
    let address = assumptions as *const PureFactContext as usize;
    ASSUMPTIONS_ID_SCOPES.with(|scopes| {
        scopes
            .borrow()
            .iter()
            .rev()
            .find(|(scope_address, _)| *scope_address == address)
            .map(|(_, id)| apply_attempt_salt(memo_id_with_logical_reads(*id, assumptions)))
    })
}

impl Drop for PureFactContextIdScope {
    fn drop(&mut self) {
        if self.pushed {
            ASSUMPTIONS_ID_SCOPES.with(|scopes| {
                scopes.borrow_mut().pop();
            });
        }
    }
}

thread_local! {
    static ATTEMPT_SALT_STACK: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    static NEXT_ATTEMPT_SALT: Cell<u64> = const { Cell::new(1) };
}

/// Runs one candidate search attempt whose memo footprint must not outlive a
/// discarded result. Every reasoning memo keys by an assumptions memo id;
/// inside an attempt those ids are salted with a fresh per-attempt value, so
/// entries the attempt writes land in a namespace no later lookup consults.
/// A discarded attempt therefore cannot perturb a later search's
/// order-sensitive selection by transporting answers computed under its own
/// budget. The trade is that attempts run memo-cold (they see none of the
/// ambient warmth and leave none behind, kept or discarded); `keep` exists
/// so callers state intent, and a kept attempt's semantic products are its
/// returned certificates, never its cache side effects.
pub(crate) fn with_search_attempt_rollback<T>(body: impl FnOnce() -> (T, bool)) -> T {
    let salt = NEXT_ATTEMPT_SALT.with(|next| {
        let salt = next.get();
        next.set(salt + 1);
        salt
    });
    ATTEMPT_SALT_STACK.with(|stack| stack.borrow_mut().push(salt));
    let (value, _keep) = body();
    ATTEMPT_SALT_STACK.with(|stack| {
        stack
            .borrow_mut()
            .pop()
            .expect("attempt salt frames are push/pop balanced");
    });
    value
}

/// The active attempt's memo-id salt, mixed into every assumptions memo id
/// so attempt-scoped entries stay invisible outside the attempt. Zero when
/// no attempt is active, preserving all ids exactly as before.
fn attempt_memo_salt() -> u64 {
    ATTEMPT_SALT_STACK.with(|stack| stack.borrow().last().copied().unwrap_or(0))
}

fn apply_attempt_salt(id: u64) -> u64 {
    let salt = attempt_memo_salt();
    if salt == 0 {
        id
    } else {
        // Multiply-xor folds the salt into the id without colliding with
        // unsalted ids drawn from the small dense counter space.
        id ^ salt.wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
}

/// Records an exact-query cycle cut or an observed verification limit.
/// Enclosing memo layers compare epochs to avoid retaining negative answers
/// produced by incomplete reasoning. Positive evidence remains valid.
pub(super) fn note_incomplete_reasoning() {
    INCOMPLETE_REASONING_EPOCH.with(|count| count.set(count.get() + 1));
}

/// Monotonic, thread-local epoch shared by all incomplete reasoning paths.
/// This is not a work budget and never limits a query.
pub(super) fn incomplete_reasoning_epoch() -> u64 {
    INCOMPLETE_REASONING_EPOCH.with(Cell::get)
}

/// Kernel checkpoint: retain the limit signal for enclosing negative memos.
/// The instrumentation checkpoint also checks deterministic tactic work and
/// retains diagnostics for the outer verification error boundary. Call it
/// exactly once so this wrapper does not change checkpoint work accounting.
pub(crate) fn reasoning_interrupted() -> bool {
    let interrupted = crate::instrumentation::deadline_exceeded();
    if interrupted {
        note_incomplete_reasoning();
    }
    interrupted
}

/// Whether the verification deadline has passed, noted as a truncation so
/// the memo layers do not cache an answer the deadline cut short. A solve
/// derivation has no step budget of its own: its decisions are memoized
/// per condition and cycle-cut, its recursion follows the proposition, and
/// its premise selection is bounded by the candidate facts, so its work is
/// bounded by the goal and the facts the goal names.
pub(crate) fn solve_reasoning_interrupted() -> bool {
    reasoning_interrupted()
}

/// Marks a condition whose fact-based solve proof is in progress. Proving a
/// condition from the proposition facts can decide other conditions, which
/// consult the facts again; a condition met again while its own proof is
/// in progress is a cycle through the facts and proves nothing on that
/// path. Distinct conditions nest freely, bounded by the conditions the
/// facts connect to the query.
struct SelectedFactReasoningGuard {
    key: (ConditionTerm, bool),
}

impl SelectedFactReasoningGuard {
    fn enter(condition: &ConditionTerm, value: bool) -> Option<Self> {
        let key = (condition.clone(), value);
        let entered = SOLVE_FACT_CONDITIONS_IN_PROGRESS
            .with(|conditions| conditions.borrow_mut().insert(key.clone()));
        if !entered {
            // Refusing the repeated query makes any enclosing negative
            // answer path-dependent, so it must not populate a memo.
            note_incomplete_reasoning();
            return None;
        }
        Some(Self { key })
    }
}

impl Drop for SelectedFactReasoningGuard {
    fn drop(&mut self) {
        SOLVE_FACT_CONDITIONS_IN_PROGRESS.with(|conditions| {
            conditions.borrow_mut().remove(&self.key);
        });
    }
}

/// A condition already being proved from the facts refuses re-entry, records
/// incomplete reasoning without unregistering the outer proof, and distinct
/// conditions nest.
#[cfg(test)]
#[test]
fn solve_fact_reasoning_guard_refuses_reentry_and_keeps_the_outer_proof() {
    let first = ConditionTerm::equal(
        MachineTerm::Variable(Variable(7_400_000)),
        MachineTerm::constant(1),
    );
    let second = ConditionTerm::equal(
        MachineTerm::Variable(Variable(7_400_001)),
        MachineTerm::constant(2),
    );
    let epoch_before = incomplete_reasoning_epoch();
    let outer = SelectedFactReasoningGuard::enter(&first, true).expect("the first proof registers");
    assert!(
        SelectedFactReasoningGuard::enter(&first, true).is_none(),
        "re-entering the condition is a cycle"
    );
    assert_eq!(
        incomplete_reasoning_epoch(),
        epoch_before + 1,
        "the cycle makes an enclosing negative answer unsafe to memoize"
    );
    let nested = SelectedFactReasoningGuard::enter(&second, true);
    assert!(nested.is_some(), "a distinct condition nests");
    assert!(
        SelectedFactReasoningGuard::enter(&first, false).is_some(),
        "the other polarity is a distinct proof"
    );
    drop(nested);
    assert!(
        SelectedFactReasoningGuard::enter(&first, true).is_none(),
        "the refused re-entry left the outer proof registered"
    );
    assert_eq!(
        incomplete_reasoning_epoch(),
        epoch_before + 2,
        "each refused query advances the incompleteness epoch"
    );
    drop(outer);
    assert!(SelectedFactReasoningGuard::enter(&first, true).is_some());
}

struct ConditionDecisionGuard {
    key: (Option<MachineIntegerType>, ConditionTerm),
}

impl ConditionDecisionGuard {
    // Order matching can compare memory loads, which can ask alias questions
    // whose pointer arithmetic re-enters the original order query. Repeating
    // an in-progress query cannot add evidence, so stop that branch
    // conservatively instead of recursing through the Rust stack.
    fn enter(condition: &ConditionTerm) -> Option<Self> {
        // Fact identity equates a narrow comparison with its promoted
        // spelling. Decision dispatch must still visit that wider carrier:
        // its indexed order authority lives there. Retain the written format
        // in the cycle key, while repeated queries at either format remain
        // blocked, including a wider query that returns to the narrow one.
        let format = match condition {
            ConditionTerm::Compare { format, .. } => Some(*format),
            _ => None,
        };
        let key = (format, condition.clone());
        CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| {
            let mut in_progress = in_progress.borrow_mut();
            if !in_progress.insert(key.clone()) {
                note_incomplete_reasoning();
                return None;
            }
            Some(Self { key })
        })
    }
}

impl Drop for ConditionDecisionGuard {
    fn drop(&mut self) {
        CONDITION_DECISIONS_IN_PROGRESS.with(|in_progress| {
            in_progress.borrow_mut().remove(&self.key);
        });
    }
}

#[test]
fn condition_decision_cycle_guard_allows_promotion_but_blocks_reentry() {
    let narrow = ConditionTerm::narrow_compare(
        MachineIntegerType::UInt8,
        CompareRelation::LessEqual,
        MachineTerm::narrow_constant(MachineIntegerType::UInt8, 48),
        MachineTerm::Variable(Variable(982899)),
    );
    let wide = crate::kernel::machine_integer::comparison::narrow_fact_widening(&narrow)
        .expect("narrow comparison");
    assert_eq!(narrow, wide, "both spellings denote the same fact");
    let outer = ConditionDecisionGuard::enter(&narrow).unwrap();
    let promoted = ConditionDecisionGuard::enter(&wide).unwrap();
    assert!(ConditionDecisionGuard::enter(&wide).is_none());
    assert!(ConditionDecisionGuard::enter(&narrow).is_none());
    drop(promoted);
    assert!(ConditionDecisionGuard::enter(&wide).is_some());
    drop(outer);
    assert!(ConditionDecisionGuard::enter(&narrow).is_some());
}

/// Pointer-offset equality up to exact materialization: two forms of one
/// offset whose embedded loads resolve, cell by known cell, to the same
/// innermost term. Deterministic and assumption-free; never equates loads
/// across an unresolved havoc.
pub(in crate::kernel) fn pointer_offsets_equal_after_exact_materialization(
    left: &AddressOffset,
    right: &AddressOffset,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            AddressOffset::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            AddressOffset::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            if left_width != right_width {
                return false;
            }
            let left = exact_materialized_index_fixed_point(left_value);
            let right = exact_materialized_index_fixed_point(right_value);
            let left_view = left.operand_view();
            let right_view = right.operand_view();
            let equal = match (left_view, right_view) {
                (MachineOperandView::Legacy(a), MachineOperandView::Legacy(b)) => a == b,
                _ => crate::kernel::shared_machine_syntax_equal(
                    &crate::kernel::KernelTerm::retained_machine_operand(
                        MachineIntegerType::Int32,
                        left_view,
                    ),
                    &crate::kernel::KernelTerm::retained_machine_operand(
                        MachineIntegerType::Int32,
                        right_view,
                    ),
                ),
            };
            equal || loads_equal_by_bounded_state_match(left_view, right_view)
        }
        (AddressOffset::Add(left_a, left_b), AddressOffset::Add(right_a, right_b)) => {
            (pointer_offsets_equal_after_exact_materialization(left_a, right_a)
                && pointer_offsets_equal_after_exact_materialization(left_b, right_b))
                || (pointer_offsets_equal_after_exact_materialization(left_a, right_b)
                    && pointer_offsets_equal_after_exact_materialization(left_b, right_a))
        }
        _ => false,
    }
}

/// Two irreducible loads of the same cell whose memory forms differ only
/// by materialization drift: chase each load to its fixed point, then let the
/// bounded state matcher decide the memory pair at that one cell. Havoc
/// markers must match on both sides, so this never equates loads across an
/// unresolved havoc. Assumption-free.
fn loads_equal_by_bounded_state_match(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> bool {
    let (Some(left), Some(right)) = (left.read_source(), right.read_source()) else {
        return false;
    };
    let (Some(left_load), Some(right_load)) = (
        crate::kernel::eval::viewed_as_memory_load(&left),
        crate::kernel::eval::viewed_as_memory_load(&right),
    ) else {
        return false;
    };
    let (
        MachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
        MachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (&left_load, &right_load)
    else {
        return false;
    };
    left_pointer == right_pointer
        && left_kind == right_kind
        && !crate::kernel::reasoning::loads_lack_recorded_equality(
            left_memory.shared_memory(),
            right_memory.shared_memory(),
            left_pointer,
            *left_kind,
            &PureFactContext::new(),
        )
        && crate::kernel::reasoning::memories_match_for_pointer_load_under_assumptions(
            left_memory.shared_memory(),
            right_memory.shared_memory(),
            left_pointer,
            &PureFactContext::new(),
        )
}

/// Only a root int32 read is materialized by this rule. Arithmetic, other
/// read kinds and unresolved states keep their written operand.
fn exact_materialized_index_fixed_point(
    term: &SharedMachineIntegerTerm,
) -> SharedMachineIntegerTerm {
    let view = term.operand_view();
    if !matches!(view.read(), Some((_, _, LoadKind::Int32))) {
        return term.clone();
    }
    let source = view.read_source().expect("selected root read");
    let result = exact_materialized_load_fixed_point(&source);
    term.with_mapped_index(result)
}

#[cfg(test)]
fn bitvector_terms_equal_after_exact_materialization(
    left: &MachineTerm,
    right: &MachineTerm,
) -> bool {
    exact_materialized_load_fixed_point(left) == exact_materialized_load_fixed_point(right)
}

fn exact_materialized_load_fixed_point(term: &MachineTerm) -> MachineTerm {
    let mut current = term.clone();
    let mut visited = std::collections::HashSet::new();
    while visited.insert(current.clone()) {
        crate::instrumentation::record_deterministic_work(1);
        let MachineTerm::MemoryLoad(memory, pointer, LoadKind::Int32) = &current else {
            break;
        };
        let Some(ProgramValue::Int32(value)) = memory.shared_memory().known_value(pointer) else {
            break;
        };
        current = value;
    }
    current
}

#[cfg(test)]
mod exact_materialization_tests {
    use super::*;

    fn load_chain(length: usize, tail: u32) -> MachineTerm {
        let pointer = Address {
            base: "exact-load-chain".into(),
            offset: AddressOffset::Constant(0),
        };
        (0..length).fold(MachineTerm::constant(tail), |value, _| {
            let memory = SymbolicMemory::new().store(pointer.clone(), ProgramValue::Int32(value));
            MachineTerm::MemoryLoad(
                ProgramPoint::at(&(intern_memory(memory))),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        })
    }

    fn index(value: MachineTerm, shared: bool) -> AddressOffset {
        let format = MachineIntegerType::Int32;
        let value = if shared {
            let root = crate::kernel::KernelTerm::retained_machine_operand(
                format,
                MachineOperandView::Legacy(&value),
            );
            SharedMachineIntegerTerm::from_shared(format, root).unwrap()
        } else {
            SharedMachineIntegerTerm::intern(format, value)
        };
        AddressOffset::Int32Scaled {
            value,
            byte_width: 4,
        }
    }

    #[test]
    fn retained_materialization_preserves_root_only_rules_and_read_kinds() {
        use crate::kernel::{KernelTermExport, MachineBinaryOp};
        let _session = crate::kernel::VerificationSession::enter();
        let chain = load_chain(8, 17);
        let add = |value| MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(value),
            right: Box::new(MachineTerm::Variable(Variable(994551))),
        };
        let pointer = Address {
            base: "exact-kind-control".into(),
            offset: AddressOffset::Constant(0),
        };
        let unsigned = MachineTerm::MemoryLoad(
            ProgramPoint::at(
                &(intern_memory(
                    SymbolicMemory::new()
                        .store(pointer.clone(), ProgramValue::UInt32(17u32.into())),
                )),
            ),
            Box::new(pointer),
            LoadKind::UInt32,
        );
        for (left, right, expected) in [
            (chain.clone(), 17u32.into(), true),
            (chain.clone(), 18u32.into(), false),
            (add(chain.clone()), add(17u32.into()), false),
            (add(chain.clone()), add(chain), true),
            (unsigned, 17u32.into(), false),
            (
                MachineTerm::constant(17),
                MachineTerm::uint32_constant(17),
                false,
            ),
        ] {
            for shared_left in [false, true] {
                for shared_right in [false, true] {
                    let left = index(left.clone(), shared_left);
                    let right = index(right.clone(), shared_right);
                    let exports = KernelTermExport::machine_export_count();
                    assert_eq!(
                        pointer_offsets_equal_after_exact_materialization(&left, &right),
                        expected
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn retained_materialization_preserves_state_separation_and_havoc() {
        use crate::kernel::KernelTermExport;
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address {
            base: "retained-retained_state".into(),
            offset: AddressOffset::Constant(0),
        };
        let other = Address {
            base: pointer.base.clone(),
            offset: AddressOffset::Constant(32),
        };
        let before = SymbolicMemory::new().with_block("retained-retained_state", 64);
        let load = |memory| {
            MachineTerm::MemoryLoad(
                ProgramPoint::at(&(intern_memory(memory))),
                Box::new(pointer.clone()),
                LoadKind::Int32,
            )
        };
        for (after, expected) in [
            (
                before
                    .clone()
                    .store(other, ProgramValue::Int32(9u32.into())),
                true,
            ),
            (
                before
                    .clone()
                    .store(pointer.clone(), ProgramValue::Int32(9u32.into())),
                false,
            ),
            (before.clone().with_block("havoc:994554", 0), false),
        ] {
            for shared_left in [false, true] {
                for shared_right in [false, true] {
                    let left = index(load(before.clone()), shared_left);
                    let right = index(load(after.clone()), shared_right);
                    let exports = KernelTermExport::machine_export_count();
                    assert_eq!(
                        pointer_offsets_equal_after_exact_materialization(&left, &right),
                        expected
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn exact_materialization_follows_an_acyclic_chain_past_the_old_hop_limit() {
        let chain = load_chain(80, 17);
        assert_eq!(
            exact_materialized_load_fixed_point(&chain),
            MachineTerm::constant(17)
        );
        assert!(bitvector_terms_equal_after_exact_materialization(
            &chain,
            &MachineTerm::constant(17)
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/exact_materialization_tests.rs");
    }
}

pub(crate) fn proposition_has_free_bitvector_variable(
    proposition: &Proposition,
    variable: Variable,
) -> bool {
    match proposition {
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            proposition_has_free_bitvector_variable(left, variable)
                || proposition_has_free_bitvector_variable(right, variable)
        }
        Proposition::Not(body) => proposition_has_free_bitvector_variable(body, variable),
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            *var != variable && proposition_has_free_bitvector_variable(body, variable)
        }
        proposition => {
            let mut variables = BTreeSet::new();
            collect_proposition_bitvector_variables(proposition, &mut variables);
            variables.contains(&variable)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum SignedConstantResolution {
    Unknown,
    Known(i64),
    Ambiguous,
}

impl SignedConstantResolution {
    pub(in crate::kernel) fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Ambiguous, _) | (_, Self::Ambiguous) => Self::Ambiguous,
            (Self::Unknown, resolution) | (resolution, Self::Unknown) => resolution,
            (Self::Known(left), Self::Known(right)) if left == right => Self::Known(left),
            (Self::Known(_), Self::Known(_)) => Self::Ambiguous,
        }
    }

    pub(in crate::kernel) fn from_term(term: MachineTerm) -> Self {
        signed_bitvector_constant(&term).map_or(Self::Unknown, Self::Known)
    }

    pub(in crate::kernel) fn map(self, operation: impl FnOnce(i64) -> MachineTerm) -> Self {
        match self {
            Self::Known(value) => Self::from_term(operation(value)),
            Self::Unknown => Self::Unknown,
            Self::Ambiguous => Self::Ambiguous,
        }
    }
}

pub(in crate::kernel) fn memory_blind_pointer_fingerprint(pointer: &Address) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hash_memory_blind_pointer(pointer, &mut hasher);
    std::hash::Hasher::finish(&hasher)
}

fn hash_memory_blind_pointer<H: std::hash::Hasher>(pointer: &Address, hasher: &mut H) {
    std::hash::Hash::hash(&pointer.base, hasher);
    hash_memory_blind_pointer_offset(&pointer.offset, hasher);
}

fn hash_memory_blind_pointer_offset<H: std::hash::Hasher>(offset: &AddressOffset, hasher: &mut H) {
    std::hash::Hash::hash(&std::mem::discriminant(offset), hasher);
    match offset {
        AddressOffset::Constant(value) => std::hash::Hash::hash(value, hasher),
        AddressOffset::Variable(variable) => std::hash::Hash::hash(variable, hasher),
        AddressOffset::Add(left, right) => {
            hash_memory_blind_pointer_offset(left, hasher);
            hash_memory_blind_pointer_offset(right, hasher);
        }
        AddressOffset::Int32Scaled { value, byte_width }
        | AddressOffset::Int64Scaled {
            value, byte_width, ..
        } => {
            std::hash::Hash::hash(
                &memory_blind_operand_fingerprint(value.operand_view()),
                hasher,
            );
            std::hash::Hash::hash(byte_width, hasher);
        }
    }
}

thread_local! {
    // Syntax only: no cached proof authority or registry interpretation.
    static OPERAND_FINGERPRINTS: RefCell<std::collections::HashMap<(OperandFingerprintPolicy, u64), u64>> =
        RefCell::new(std::collections::HashMap::new());
}

// Child fingerprints keep repeated shared subexpressions compact. The same
// operand-view encoding is used for native and shared index syntax; states
// are omitted only along the paths allowed by the selected policy.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum OperandFingerprintPolicy {
    MemoryBlind,
    MemoryState(bool),
}
impl OperandFingerprintPolicy {
    fn without_frame(self) -> Self {
        match self {
            Self::MemoryBlind => self,
            Self::MemoryState(_) => Self::MemoryState(false),
        }
    }
}
/// Exact-syntax candidate fingerprint. Collisions are not proof authority.
/// Arithmetic nodes are memoized; states and native opaque payloads remain
/// in the key, unlike the framed and memory-blind candidate policies.
pub(in crate::kernel) fn machine_syntax_fingerprint(root: MachineOperandView<'_>) -> u64 {
    operand_fingerprint(root, OperandFingerprintPolicy::MemoryState(false))
}

fn memory_blind_operand_fingerprint(root: MachineOperandView<'_>) -> u64 {
    operand_fingerprint(root, OperandFingerprintPolicy::MemoryBlind)
}
fn operand_fingerprint(root: MachineOperandView<'_>, policy: OperandFingerprintPolicy) -> u64 {
    use std::hash::{Hash, Hasher};
    let key = |policy, value: MachineOperandView<'_>| match value {
        MachineOperandView::Shared(term) => (policy, true, term.id()),
        MachineOperandView::Legacy(term) => {
            (policy, false, term as *const MachineTerm as usize as u64)
        }
    };
    let mut values = std::collections::HashMap::new();
    let mut pending = vec![(policy, root, false)];
    while let Some((policy, value, finish)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if values.contains_key(&key(policy, value)) {
            continue;
        }
        if let MachineOperandView::Shared(term) = value
            && let Some(hash) =
                OPERAND_FINGERPRINTS.with(|memo| memo.borrow().get(&(policy, term.id())).copied())
        {
            values.insert(key(policy, value), hash);
            continue;
        }
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        if let Some((source, destination, operand)) = float_conversions::machine_conversion(value) {
            4u8.hash(&mut hash);
            source.hash(&mut hash);
            destination.hash(&mut hash);
            float_conversions::fingerprint(operand, policy.without_frame()).hash(&mut hash);
            let hash = hash.finish();
            values.insert(key(policy, value), hash);
            if let MachineOperandView::Shared(root) = value {
                OPERAND_FINGERPRINTS
                    .with(|memo| memo.borrow_mut().insert((policy, root.id()), hash));
            }
            continue;
        }
        let (child_policy, children) = if let Some((format, op, args)) = value.binary() {
            0u8.hash(&mut hash);
            format.hash(&mut hash);
            op.hash(&mut hash);
            let child_policy = match policy {
                OperandFingerprintPolicy::MemoryBlind => policy,
                OperandFingerprintPolicy::MemoryState(frame) => {
                    OperandFingerprintPolicy::MemoryState(
                        frame
                            && format.format().bits() == 32
                            && matches!(
                                op,
                                crate::kernel::MachineBinaryOp::Add
                                    | crate::kernel::MachineBinaryOp::Subtract
                                    | crate::kernel::MachineBinaryOp::Multiply
                            ),
                    )
                }
            };
            (child_policy, args.to_vec())
        } else if let Some((format, op, arg)) = value.unary() {
            1u8.hash(&mut hash);
            format.hash(&mut hash);
            op.hash(&mut hash);
            (policy.without_frame(), vec![arg])
        } else if let Some((encoding, source, destination, arg)) = value.cast() {
            2u8.hash(&mut hash);
            encoding.hash(&mut hash);
            source.hash(&mut hash);
            destination.hash(&mut hash);
            (policy.without_frame(), vec![arg])
        } else {
            3u8.hash(&mut hash);
            if let (OperandFingerprintPolicy::MemoryState(true), Some(kind)) =
                (policy, value.read_kind())
            {
                // This selector observes only the kind. Exporting its address
                // would add cold-cache work to an otherwise fixed root query.
                kind.hash(&mut hash);
            } else {
                let leaf = value
                    .literal()
                    .map(std::borrow::Cow::Owned)
                    .unwrap_or_else(|| value.read_source().expect("retained machine leaf"));
                match (policy, leaf.as_ref()) {
                    (OperandFingerprintPolicy::MemoryBlind, _) => {
                        hash_memory_blind_bitvector(&leaf, &mut hash)
                    }
                    (
                        OperandFingerprintPolicy::MemoryState(true),
                        MachineTerm::MemoryLoad(_, _, kind),
                    ) => kind.hash(&mut hash),
                    (OperandFingerprintPolicy::MemoryState(_), _) => leaf.hash(&mut hash),
                }
            }
            let hash = hash.finish();
            values.insert(key(policy, value), hash);
            if let MachineOperandView::Shared(term) = value {
                OPERAND_FINGERPRINTS
                    .with(|memo| memo.borrow_mut().insert((policy, term.id()), hash));
            }
            continue;
        };
        if !finish {
            pending.push((policy, value, true));
            pending.extend(
                children
                    .into_iter()
                    .map(|child| (child_policy, child, false)),
            );
        } else {
            for child in children {
                values[&key(child_policy, child)].hash(&mut hash);
            }
            let hash = hash.finish();
            values.insert(key(policy, value), hash);
            if let MachineOperandView::Shared(term) = value {
                OPERAND_FINGERPRINTS
                    .with(|memo| memo.borrow_mut().insert((policy, term.id()), hash));
            }
        }
    }
    values[&key(policy, root)]
}

fn hash_memory_blind_condition<H: std::hash::Hasher>(condition: &ConditionTerm, hasher: &mut H) {
    std::hash::Hash::hash(&std::mem::discriminant(condition), hasher);
    match condition {
        ConditionTerm::PointerEqual(left, right) => {
            std::hash::Hash::hash(left, hasher);
            std::hash::Hash::hash(right, hasher);
        }

        ConditionTerm::Constant(value) => std::hash::Hash::hash(value, hasher),
        ConditionTerm::AlgebraicEqual(left, right) => {
            std::hash::Hash::hash(left, hasher);
            std::hash::Hash::hash(right, hasher);
        }
        ConditionTerm::Variable(variable) => std::hash::Hash::hash(variable, hasher),
        crate::kernel::binary_bitvector_condition!(left, right) => {
            hash_memory_blind_bitvector(left, hasher);
            hash_memory_blind_bitvector(right, hasher);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            std::hash::Hash::hash(float_condition, hasher);
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            hash_memory_blind_pointer_offset(left, hasher);
            hash_memory_blind_pointer_offset(right, hasher);
        }
        ConditionTerm::AddressEqual(left, right) => {
            hash_memory_blind_pointer(left, hasher);
            hash_memory_blind_pointer(right, hasher);
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            std::hash::Hash::hash(left, hasher);
            std::hash::Hash::hash(right, hasher);
        }
        // An application's arguments are hashed whole, as a word-valued
        // Click application's are.
        ConditionTerm::BoolApplication(application) => {
            std::hash::Hash::hash(application, hasher);
        }
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            hash_memory_blind_condition(condition, hasher);
            hash_memory_blind_condition(then_condition, hasher);
            hash_memory_blind_condition(else_condition, hasher);
        }
        ConditionTerm::BoolEqual(left, right) => {
            hash_memory_blind_condition(left, hasher);
            hash_memory_blind_condition(right, hasher);
        }
        ConditionTerm::BoolLoad(_, pointer) => hash_memory_blind_pointer(pointer, hasher),
    }
}

fn hash_memory_blind_bitvector<H: std::hash::Hasher>(term: &MachineTerm, hasher: &mut H) {
    std::hash::Hash::hash(&std::mem::discriminant(term), hasher);
    // One variant spells every constant, so its format is hashed as the
    // constant shapes' discriminants were.
    if let MachineTerm::Constant { format, .. } = term {
        std::hash::Hash::hash(format, hasher);
    }
    // So is a conversion's spelling, as the per-pair variants were.
    if let MachineTerm::Cast { spelling, .. } = term {
        std::hash::Hash::hash(spelling, hasher);
    }
    match term {
        MachineTerm::ThreadHandle(id) => std::hash::Hash::hash(id, hasher),
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            from: source,
            to: destination,
        } => {
            std::hash::Hash::hash(source, hasher);
            std::hash::Hash::hash(destination, hasher);
            hash_memory_blind_bitvector(value, hasher);
        }
        MachineTerm::BoolCast { to, value } => {
            std::hash::Hash::hash(to, hasher);
            hash_memory_blind_condition(value, hasher);
        }

        int32_constant!(value) => std::hash::Hash::hash(&constant_u32(*value), hasher),
        uint32_constant!(value) => {
            std::hash::Hash::hash("uint32", hasher);
            std::hash::Hash::hash(&constant_u32(*value), hasher)
        }
        int64_constant!(value) => std::hash::Hash::hash(&constant_i64(*value), hasher),
        uint64_constant!(value) => std::hash::Hash::hash(&constant_u64(*value), hasher),
        native_constant!(_, _) => std::hash::Hash::hash(&term.as_machine_constant(), hasher),
        MachineTerm::Variable(variable) => std::hash::Hash::hash(variable, hasher),
        MachineTerm::MemoryLoad(_, pointer, kind) => {
            std::hash::Hash::hash(kind, hasher);
            hash_memory_blind_pointer(pointer, hasher)
        }
        MachineTerm::IntegerAddress(pointer, _) => {
            std::hash::Hash::hash("address", hasher);
            hash_memory_blind_pointer(pointer, hasher)
        }
        crate::kernel::binary_bitvector32_term!(left, right) => {
            std::hash::Hash::hash(&term.machine_operator(), hasher);
            hash_memory_blind_bitvector(left, hasher);
            hash_memory_blind_bitvector(right, hasher);
        }
        cast_term!(Int64From32, value)
        | cast_term!(Int64FromUInt32, value)
        | cast_term!(UInt64From32, value)
        | cast_term!(UInt32From64, value)
        | cast_term!(UInt64FromInt32, value)
        | cast_term!(UInt64FromInt64, value) => hash_memory_blind_bitvector(value, hasher),
        MachineTerm::Unary {
            format,
            op,
            operand,
        } => {
            std::hash::Hash::hash(format, hasher);
            std::hash::Hash::hash(op, hasher);
            hash_memory_blind_bitvector(operand, hasher)
        }
        MachineTerm::Binary {
            format,
            op,
            left,
            right,
        } => {
            std::hash::Hash::hash(format, hasher);
            std::hash::Hash::hash(op, hasher);
            hash_memory_blind_bitvector(left, hasher);
            hash_memory_blind_bitvector(right, hasher);
        }
        MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            hash_memory_blind_bitvector(left, hasher);
            hash_memory_blind_bitvector(right, hasher);
        }
        MachineTerm::Float32Negate(value) | MachineTerm::Float64Negate(value) => {
            hash_memory_blind_bitvector(value, hasher)
        }
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            hash_memory_blind_condition(condition, hasher);
            hash_memory_blind_bitvector(then_term, hasher);
            hash_memory_blind_bitvector(else_term, hasher);
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            hash_memory_blind_bitvector(start, hasher);
            hash_memory_blind_bitvector(end, hasher);
            hash_memory_blind_bitvector(initial, hasher);
            std::hash::Hash::hash(accumulator, hasher);
            std::hash::Hash::hash(item, hasher);
            hash_memory_blind_bitvector(body, hasher);
        }
        MachineTerm::PureFunctionApplication { name, arguments } => {
            std::hash::Hash::hash(name, hasher);
            for argument in arguments {
                hash_memory_blind_bitvector(argument, hasher);
            }
        }
        MachineTerm::ClickFunctionApplication { .. } | MachineTerm::AlgebraicMatch { .. } => {
            std::hash::Hash::hash(term, hasher)
        }
        MachineTerm::IntegerToMachine { value, destination } => {
            std::hash::Hash::hash(destination, hasher);
            std::hash::Hash::hash(value, hasher);
        }
    }
}

fn collect_condition_memory_load_keys(
    condition: &ConditionTerm,
    keys: &mut BTreeSet<(AddressBase, u64)>,
) {
    let mut collect_binary = |left: &MachineTerm, right: &MachineTerm| {
        collect_bitvector_memory_load_keys(left, keys);
        collect_bitvector_memory_load_keys(right, keys);
    };
    match condition {
        ConditionTerm::PointerEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_offset_memory_load_keys(&pointer.offset, keys);
            }
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_machine_operand(|view| {
                visit_machine_operand_scoped_leaves(view, |term| {
                    collect_scoped_leaf_memory_load_keys(term, keys)
                })
            });
            right.for_each_machine_operand(|view| {
                visit_machine_operand_scoped_leaves(view, |term| {
                    collect_scoped_leaf_memory_load_keys(term, keys)
                })
            });
        }
        crate::kernel::binary_bitvector_condition!(left, right) => collect_binary(left, right),
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition
                .for_each_bitvector_term(|term| collect_bitvector_memory_load_keys(term, keys));
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_memory_load_keys(left, keys);
            collect_pointer_offset_memory_load_keys(right, keys);
        }
        ConditionTerm::AddressEqual(left, right) => {
            collect_pointer_offset_memory_load_keys(&left.offset, keys);
            collect_pointer_offset_memory_load_keys(&right.offset, keys);
        }
        crate::kernel::integer_comparison_condition!(_, _) => {}
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        // As a word-valued Click application's: its arguments are not keyed.
        ConditionTerm::BoolApplication(_) => {}
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_memory_load_keys(condition, keys);
            }
        }
        ConditionTerm::BoolEqual(left, right) => {
            collect_condition_memory_load_keys(left, keys);
            collect_condition_memory_load_keys(right, keys);
        }
        ConditionTerm::BoolLoad(_, pointer) => {
            keys.insert((
                pointer.base.clone(),
                memory_blind_pointer_fingerprint(pointer),
            ));
            collect_pointer_offset_memory_load_keys(&pointer.offset, keys);
        }
    }
}

fn collect_pointer_offset_memory_load_keys(
    offset: &AddressOffset,
    keys: &mut BTreeSet<(AddressBase, u64)>,
) {
    offset.for_each_scaled_operand(|value| {
        visit_machine_operand_scoped_leaves(value.operand_view(), |leaf| {
            collect_scoped_leaf_memory_load_keys(leaf, keys)
        })
    });
}

fn collect_scoped_leaf_memory_load_keys(
    leaf: MachineOperandView<'_>,
    keys: &mut BTreeSet<(AddressBase, u64)>,
) {
    if let MachineOperandView::Shared(root) = leaf
        && matches!(root.node(), KernelTermNode::FloatConvert { .. })
    {
        float_conversions::collect_load_keys(root, keys);
        return;
    }
    if let MachineOperandView::Shared(root) = leaf
        && let KernelTermNode::Fold(fold) = root.node()
    {
        for child in &fold.arguments {
            visit_machine_operand_scoped_leaves(MachineOperandView::Shared(child), |leaf| {
                collect_scoped_leaf_memory_load_keys(leaf, keys)
            });
        }
    } else {
        collect_bitvector_memory_load_keys(&leaf.read_source().expect("native scoped leaf"), keys);
    }
}

fn collect_bitvector_memory_load_keys(term: &MachineTerm, keys: &mut BTreeSet<(AddressBase, u64)>) {
    match term {
        MachineTerm::ThreadHandle(_) => {}
        bits32_constant!(_)
        | MachineTerm::Variable(_)
        | int64_constant!(_)
        | uint64_constant!(_)
        | native_constant!(_, _) => {}
        MachineTerm::MemoryLoad(_, pointer, kind) => {
            // Integer reads name fixed versions, just as the former reserved
            // variables did. This legacy load-time transport index is only
            // for the remaining non-integer read families. Rebuilding an
            // integer descriptor must not launch history searches to retarget
            // facts about it. Explicit transport and step-produced frame
            // equalities retain their ordinary evidence routes.
            if !matches!(kind, LoadKind::Float32 | LoadKind::Float64) {
                return;
            }
            keys.insert((
                pointer.base.clone(),
                memory_blind_pointer_fingerprint(pointer),
            ));
            collect_pointer_offset_memory_load_keys(&pointer.offset, keys);
        }
        MachineTerm::IntegerAddress(pointer, _) => {
            collect_pointer_offset_memory_load_keys(&pointer.offset, keys);
        }
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memory_load_keys(condition, keys);
            collect_bitvector_memory_load_keys(then_term, keys);
            collect_bitvector_memory_load_keys(else_term, keys);
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_memory_load_keys(start, keys);
            collect_bitvector_memory_load_keys(end, keys);
            collect_bitvector_memory_load_keys(initial, keys);
            collect_bitvector_memory_load_keys(body, keys);
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_memory_load_keys(argument, keys);
            }
        }
        MachineTerm::ClickFunctionApplication { .. } | MachineTerm::AlgebraicMatch { .. } => {}
        MachineTerm::IntegerToMachine { .. } => {}
        MachineTerm::BoolCast { value, .. } => collect_condition_memory_load_keys(value, keys),
        term => {
            if let Some((_, left, right)) = term.as_binary() {
                collect_bitvector_memory_load_keys(left, keys);
                collect_bitvector_memory_load_keys(right, keys);
            } else {
                let (_, value) = term
                    .as_unary()
                    .expect("every other term is binary or unary");
                collect_bitvector_memory_load_keys(value, keys);
            }
        }
    }
}

/// Collect every current-state load nested in a lowered term.  This is the
/// boundary used by dynamic resource checking, so an unrecognised carrier is
/// an error rather than an invitation to silently forget a memory dependency.
pub(crate) fn current_memory_loads_in_term(
    term: &Term,
    current_memory: &SymbolicMemory,
) -> Result<Vec<(Address, u32)>, String> {
    let mut loads = Vec::new();
    collect_term_memory_loads(term, current_memory, &mut loads, &mut BTreeSet::new())?;
    loads.sort();
    loads.dedup();
    Ok(loads)
}

fn collect_term_memory_loads(
    term: &Term,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match term {
        Term::Condition(condition) => {
            collect_condition_memory_loads(condition, current_memory, loads, seen_integers)
        }
        Term::Bitvector32(term) => {
            collect_bitvector_memory_loads(term, current_memory, loads, None, seen_integers)
        }
        Term::Integer(term) => {
            collect_integer_memory_loads(term, current_memory, loads, seen_integers)
        }
        Term::PointerOffset(offset) => {
            collect_pointer_offset_memory_loads(offset, current_memory, loads, seen_integers)
        }
        Term::ProgramValue(value) => {
            collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)
        }
        Term::Sequence(sequence) => {
            collect_sequence_memory_loads(sequence, current_memory, loads, seen_integers)
        }
        Term::Algebraic(term) => {
            collect_algebraic_memory_loads(term, current_memory, loads, seen_integers)
        }
        Term::Memory(_) | Term::ExecutionState(_) => Ok(()),
    }
}

fn collect_condition_memory_loads(
    condition: &ConditionTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match condition {
        ConditionTerm::PointerEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_offset_memory_loads(
                    &pointer.offset,
                    current_memory,
                    loads,
                    seen_integers,
                )?;
            }
            Ok(())
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_algebraic_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_algebraic_memory_loads(right, current_memory, loads, seen_integers)
        }
        ConditionTerm::Compare {
            format,
            left,
            right,
            ..
        }
        | ConditionTerm::Overflows {
            format,
            left,
            right,
            ..
        } => {
            let width = Some(format.carrier_bytes());
            collect_bitvector_memory_loads(left, current_memory, loads, width, seen_integers)?;
            collect_bitvector_memory_loads(right, current_memory, loads, width, seen_integers)
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            let width = if matches!(condition, ConditionTerm::Float32(_)) {
                4
            } else {
                8
            };
            let mut result = Ok(());
            float_condition.for_each_bitvector_term(|term| {
                if result.is_ok() {
                    result = collect_bitvector_memory_loads(
                        term,
                        current_memory,
                        loads,
                        Some(width),
                        seen_integers,
                    );
                }
            });
            result
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_pointer_offset_memory_loads(right, current_memory, loads, seen_integers)
        }
        ConditionTerm::AddressEqual(left, right) => {
            collect_pointer_offset_memory_loads(
                &left.offset,
                current_memory,
                loads,
                seen_integers,
            )?;
            collect_pointer_offset_memory_loads(&right.offset, current_memory, loads, seen_integers)
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            collect_integer_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_integer_memory_loads(right, current_memory, loads, seen_integers)
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => Ok(()),
        ConditionTerm::BoolApplication(_) => {
            Err("opaque Click function may hide a current memory load".into())
        }
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_memory_loads(condition, current_memory, loads, seen_integers)?;
            }
            Ok(())
        }
        ConditionTerm::BoolEqual(left, right) => {
            collect_condition_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_condition_memory_loads(right, current_memory, loads, seen_integers)
        }
        // A `bool` cell is one byte.
        ConditionTerm::BoolLoad(memory, pointer) => {
            if MemoryStateIdentity::of(memory.memory()) == MemoryStateIdentity::of(current_memory) {
                loads.push((pointer.as_ref().clone(), 1));
            }
            collect_pointer_offset_memory_loads(
                &pointer.offset,
                current_memory,
                loads,
                seen_integers,
            )
        }
    }
}

fn collect_pointer_offset_memory_loads(
    offset: &AddressOffset,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match offset {
        AddressOffset::Constant(_) | AddressOffset::Variable(_) => Ok(()),
        AddressOffset::Add(left, right) => {
            collect_pointer_offset_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_pointer_offset_memory_loads(right, current_memory, loads, seen_integers)
        }
        AddressOffset::Int32Scaled { value, .. } => collect_shared_machine_memory_loads(
            value,
            current_memory,
            loads,
            Some(4),
            seen_integers,
        ),
        AddressOffset::Int64Scaled { value, .. } => collect_shared_machine_memory_loads(
            value,
            current_memory,
            loads,
            Some(8),
            seen_integers,
        ),
    }
}

fn collect_bitvector_memory_loads(
    term: &MachineTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    collect_bitvector_memory_loads_with_width(term, current_memory, loads, width, seen_integers)
}

fn collect_memory_read_descriptor(
    operand: MachineOperandView<'_>,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    let (memory, pointer, kind) = operand.read().expect("read descriptor");
    // Produced reads own an access width and observation point. Their numeric
    // interpretation can be wider (byte promotion) without widening the read.
    // Explicit unmaterialized descriptors retain their caller-supplied width.
    let observation = crate::kernel::eval::is_selected_scalar_read(memory, pointer, kind)
        .then(|| crate::kernel::eval::scalar_read_observation(operand).expect("selected read"));
    let memory = observation
        .as_ref()
        .map(|read| read.origin.as_ref().unwrap_or(&read.memory))
        .unwrap_or(memory);
    let width = observation.as_ref().map(|read| read.bytes).or(width);
    if MemoryStateIdentity::of(memory.memory()) == MemoryStateIdentity::of(current_memory) {
        let width = width
            .ok_or_else(|| "current memory load has no statically known byte width".to_string())?;
        loads.push((pointer.clone(), width));
    }
    collect_pointer_offset_memory_loads(&pointer.offset, current_memory, loads, seen_integers)
}

fn collect_bitvector_memory_loads_with_width(
    term: &MachineTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match term {
        MachineTerm::ThreadHandle(_) => Ok(()),
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            from: source,
            ..
        } => collect_bitvector_memory_loads_with_width(
            value,
            current_memory,
            loads,
            Some(source.format().byte_width()),
            seen_integers,
        ),

        bits32_constant!(_)
        | MachineTerm::Variable(_)
        | int64_constant!(_)
        | uint64_constant!(_)
        | native_constant!(_, _) => Ok(()),
        MachineTerm::MemoryLoad(..) => collect_memory_read_descriptor(
            MachineOperandView::Legacy(term),
            current_memory,
            loads,
            width,
            seen_integers,
        ),
        MachineTerm::IntegerAddress(pointer, _) => collect_pointer_offset_memory_loads(
            &pointer.offset,
            current_memory,
            loads,
            seen_integers,
        ),
        crate::kernel::binary_machine_term!(left, right)
        | MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            let child_width = if matches!(
                term,
                crate::kernel::binary_wide_term!(..) | MachineTerm::Float64Binary { .. }
            ) {
                Some(8)
            } else {
                width
            };
            collect_bitvector_memory_loads_with_width(
                left,
                current_memory,
                loads,
                child_width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                right,
                current_memory,
                loads,
                child_width,
                seen_integers,
            )
        }
        cast_term!(Int64From32, value)
        | cast_term!(Int64FromUInt32, value)
        | cast_term!(UInt64From32, value)
        | cast_term!(UInt32From64, value)
        | cast_term!(UInt64FromInt32, value)
        | cast_term!(UInt64FromInt64, value)
        | MachineTerm::Unary { operand: value, .. }
        | MachineTerm::Float32Negate(value)
        | MachineTerm::Float64Negate(value) => {
            let child_width = if matches!(term, MachineTerm::Float64Negate(_)) {
                Some(8)
            } else {
                width
            };
            collect_bitvector_memory_loads_with_width(
                value,
                current_memory,
                loads,
                child_width,
                seen_integers,
            )
        }
        MachineTerm::IntegerToMachine { value, destination } => {
            let width = Some(match destination {
                MachineIntegerType::Int8 => 1,
                MachineIntegerType::Int16 | MachineIntegerType::UInt16 => 2,
                MachineIntegerType::UInt8 => 1,
                MachineIntegerType::Int32 | MachineIntegerType::UInt32 => 4,
                MachineIntegerType::Int64 | MachineIntegerType::UInt64 => 8,
                MachineIntegerType::Int128 | MachineIntegerType::UInt128 => 16,
            });
            collect_integer_memory_loads_with_width(
                value,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        MachineTerm::BoolCast { value, .. } => {
            collect_condition_memory_loads(value, current_memory, loads, seen_integers)
        }
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memory_loads(condition, current_memory, loads, seen_integers)?;
            collect_bitvector_memory_loads_with_width(
                then_term,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                else_term,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_memory_loads_with_width(
                start,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                end,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                initial,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_bitvector_memory_loads_with_width(
                body,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            let _ = (arguments, width, seen_integers);
            Err("opaque pure function may hide a current memory load".into())
        }
        MachineTerm::ClickFunctionApplication { .. } => {
            Err("opaque Click function may hide a current memory load".into())
        }
        MachineTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_memory_loads(scrutinee, current_memory, loads, seen_integers)?;
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_memory_loads(
                        binding,
                        current_memory,
                        loads,
                        seen_integers,
                    )?;
                }
                collect_bitvector_memory_loads_with_width(
                    &arm.body,
                    current_memory,
                    loads,
                    width,
                    seen_integers,
                )?;
            }
            Ok(())
        }
    }
}

fn collect_cvalue_memory_loads(
    value: &ProgramValue,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Int128(term) | ProgramValue::UInt128(term) => {
            collect_bitvector_memory_loads_with_width(
                term,
                current_memory,
                loads,
                Some(16),
                seen_integers,
            )
        }

        ProgramValue::Parameter(term) => {
            collect_algebraic_memory_loads(term, current_memory, loads, seen_integers)
        }
        ProgramValue::Void => Ok(()),
        ProgramValue::Bool(term) | ProgramValue::UInt8(term) => {
            collect_bitvector_memory_loads_with_width(
                term,
                current_memory,
                loads,
                Some(1),
                seen_integers,
            )
        }
        ProgramValue::Int8(term) => collect_bitvector_memory_loads_with_width(
            term,
            current_memory,
            loads,
            Some(1),
            seen_integers,
        ),
        ProgramValue::Int16(term) | ProgramValue::UInt16(term) => {
            collect_bitvector_memory_loads_with_width(
                term,
                current_memory,
                loads,
                Some(2),
                seen_integers,
            )
        }
        ProgramValue::Int32(term) | ProgramValue::UInt32(term) | ProgramValue::Float32(term) => {
            collect_bitvector_memory_loads_with_width(
                term,
                current_memory,
                loads,
                Some(4),
                seen_integers,
            )
        }
        ProgramValue::Int64(term) | ProgramValue::UInt64(term) | ProgramValue::Float64(term) => {
            collect_bitvector_memory_loads_with_width(
                term,
                current_memory,
                loads,
                Some(8),
                seen_integers,
            )
        }
        ProgramValue::Pointer(pointer) => collect_pointer_offset_memory_loads(
            &pointer.address().offset,
            current_memory,
            loads,
            seen_integers,
        ),
    }
}

fn collect_sequence_memory_loads(
    sequence: &SequenceTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for value in values.iter() {
                collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)?;
            }
            Ok(())
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_memory_loads(left, current_memory, loads, seen_integers)?;
            collect_sequence_memory_loads(right, current_memory, loads, seen_integers)
        }
    }
}

fn collect_algebraic_value_memory_loads(
    value: &AlgebraicValue,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match value {
        AlgebraicValue::Program(value) => {
            collect_cvalue_memory_loads(value, current_memory, loads, seen_integers)
        }
        AlgebraicValue::Integer(value) => {
            collect_integer_memory_loads(value, current_memory, loads, seen_integers)
        }
        AlgebraicValue::Algebraic(value) => {
            collect_algebraic_memory_loads(value, current_memory, loads, seen_integers)
        }
    }
}

fn collect_algebraic_memory_loads(
    term: &AlgebraicTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match &term.node {
        AlgebraicTermNode::Variable(_) => Ok(()),
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_memory_loads(field, current_memory, loads, seen_integers)?;
            }
            Ok(())
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_memory_loads(scrutinee, current_memory, loads, seen_integers)?;
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_memory_loads(
                        binding,
                        current_memory,
                        loads,
                        seen_integers,
                    )?;
                }
                collect_algebraic_memory_loads(&arm.body, current_memory, loads, seen_integers)?;
            }
            Ok(())
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            let _ = (arguments, current_memory, loads, seen_integers);
            Err("opaque algebraic function may hide a current memory load".into())
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => collect_bitvector_memory_loads_with_width(
            &AlgebraicTermNode::memory_load_carrier(memory, pointer),
            current_memory,
            loads,
            Some(crate::kernel::ABSTRACT_VALUE_WIDTH),
            seen_integers,
        ),
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memory_loads(condition, current_memory, loads, seen_integers)?;
            collect_algebraic_memory_loads(then_term, current_memory, loads, seen_integers)?;
            collect_algebraic_memory_loads(else_term, current_memory, loads, seen_integers)
        }
    }
}

fn collect_integer_memory_loads(
    term: &IntegerTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    collect_integer_node_memory_loads(term, current_memory, loads, None, seen_integers)
}

fn collect_integer_memory_loads_with_width(
    term: &SharedIntegerTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    if !seen_integers.insert(term.id()) {
        return Ok(());
    }
    if matches!(term.as_ref(), IntegerTerm::AlgebraicMatch { .. }) {
        let root = KernelTermImport::default().integer(term);
        let KernelTermNode::Match(matched) = root.node() else {
            unreachable!("Integer match")
        };
        return retained_matches::collect_match_memory_loads(
            matched,
            current_memory,
            loads,
            width,
            seen_integers,
        );
    }
    if matches!(term.as_ref(), IntegerTerm::RangeFold { .. }) {
        let root = KernelTermImport::default().integer(term);
        let KernelTermNode::Fold(fold) = root.node() else {
            unreachable!("migrated Integer fold");
        };
        return retained_folds::collect_fold_memory_loads(
            fold,
            current_memory,
            loads,
            width,
            seen_integers,
        );
    }
    collect_integer_node_memory_loads(term.as_ref(), current_memory, loads, width, seen_integers)
}

/// Shared arithmetic retains read nodes and Integer conversion carriers.
/// Read their syntax summaries, then resolve each
/// payload against this query's state; never cache memory-dependent results.
fn collect_shared_machine_memory_loads(
    value: &SharedMachineIntegerTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    let Some(root) = value.shared_operand() else {
        return collect_bitvector_memory_loads_with_width(
            value.value(),
            current_memory,
            loads,
            width,
            seen_integers,
        );
    };
    // A selected root leaf has no shared arithmetic to summarize. Resolve it
    // directly using the existing width/state/registry rules.
    if let Some(leaf) = value.operand_view().read_source() {
        return collect_bitvector_memory_loads_with_width(
            &leaf,
            current_memory,
            loads,
            width,
            seen_integers,
        );
    }
    if value.operand_view().literal().is_some() {
        return Ok(());
    }
    collect_shared_read_memory_loads(root, current_memory, loads, width, seen_integers)?;
    let interrupted = || "memory-load collection exceeded its checking budget".to_string();
    let leaves = crate::kernel::shared_machine_conversion_leaves(root, || {
        !crate::instrumentation::deadline_exceeded()
    })
    .ok_or_else(interrupted)?;
    for (_, leaf) in leaves.iter() {
        if crate::instrumentation::deadline_exceeded() {
            return Err(interrupted());
        }
        if let KernelTermNode::Match(matched) = leaf.node() {
            retained_matches::collect_match_memory_loads(
                matched,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            continue;
        }
        if let KernelTermNode::Fold(fold) = leaf.node() {
            retained_folds::collect_fold_memory_loads(
                fold,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            continue;
        }
        if matches!(leaf.node(), KernelTermNode::FloatConvert { .. }) {
            return Err("opaque pure function may hide a current memory load".into());
        }
        // A conversion establishes its own destination width before visiting
        // the Integer payload, independently of surrounding arithmetic/casts.
        collect_bitvector_memory_loads_with_width(
            leaf.machine_conversion_leaf().expect("conversion leaf"),
            current_memory,
            loads,
            width,
            seen_integers,
        )?;
    }
    Ok(())
}

fn collect_shared_read_memory_loads(
    root: &KernelTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    let reads = crate::kernel::shared_machine_read_uses(root, width, || {
        !crate::instrumentation::deadline_exceeded_with_work(1)
    })
    .ok_or_else(|| "memory-load collection exceeded its checking budget".to_string())?;
    for ((_, width), read) in reads.iter() {
        collect_memory_read_descriptor(
            MachineOperandView::Shared(read),
            current_memory,
            loads,
            *width,
            seen_integers,
        )?;
    }
    Ok(())
}

fn collect_integer_node_memory_loads(
    term: &IntegerTerm,
    current_memory: &SymbolicMemory,
    loads: &mut Vec<(Address, u32)>,
    width: Option<u32>,
    seen_integers: &mut BTreeSet<u64>,
) -> Result<(), String> {
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => Ok(()),
        IntegerTerm::Machine(value) => collect_shared_machine_memory_loads(
            value,
            current_memory,
            loads,
            Some(match value.ty() {
                MachineIntegerType::UInt8 => 1,
                MachineIntegerType::Int8 => 1,
                MachineIntegerType::Int16 | MachineIntegerType::UInt16 => 2,
                MachineIntegerType::Int32 | MachineIntegerType::UInt32 => 4,
                MachineIntegerType::Int64 | MachineIntegerType::UInt64 => 8,
                MachineIntegerType::Int128 | MachineIntegerType::UInt128 => 16,
            }),
            seen_integers,
        ),
        IntegerTerm::Negate(value) => collect_integer_memory_loads_with_width(
            value,
            current_memory,
            loads,
            width,
            seen_integers,
        ),
        crate::kernel::binary_integer_term!(left, right) => {
            collect_integer_memory_loads_with_width(
                left,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_integer_memory_loads_with_width(
                right,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        IntegerTerm::PureFunctionApplication(application) => {
            let _ = (application, current_memory, loads, seen_integers);
            Err("opaque integer function may hide a current memory load".into())
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_memory_loads(scrutinee, current_memory, loads, seen_integers)?;
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_memory_loads(
                        binding,
                        current_memory,
                        loads,
                        seen_integers,
                    )?;
                }
                collect_integer_memory_loads_with_width(
                    &arm.body,
                    current_memory,
                    loads,
                    width,
                    seen_integers,
                )?;
            }
            Ok(())
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memory_loads(condition, current_memory, loads, seen_integers)?;
            collect_integer_memory_loads_with_width(
                then_term,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_integer_memory_loads_with_width(
                else_term,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            body,
            ..
        } => {
            match index {
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    let endpoint_width = if matches!(index, IntegerRangeFoldIndex::UInt64 { .. }) {
                        8
                    } else {
                        4
                    };
                    collect_shared_machine_memory_loads(
                        start.machine_operand(),
                        current_memory,
                        loads,
                        Some(endpoint_width),
                        seen_integers,
                    )?;
                    collect_shared_machine_memory_loads(
                        end.machine_operand(),
                        current_memory,
                        loads,
                        Some(endpoint_width),
                        seen_integers,
                    )?;
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_integer_memory_loads_with_width(
                        start,
                        current_memory,
                        loads,
                        width,
                        seen_integers,
                    )?;
                    collect_integer_memory_loads_with_width(
                        end,
                        current_memory,
                        loads,
                        width,
                        seen_integers,
                    )?;
                }
            }
            collect_integer_memory_loads_with_width(
                initial,
                current_memory,
                loads,
                width,
                seen_integers,
            )?;
            collect_integer_memory_loads_with_width(
                body,
                current_memory,
                loads,
                width,
                seen_integers,
            )
        }
    }
}

#[cfg(test)]
impl Proposition {
    pub(super) fn peel_implications(&self) -> &Self {
        match self {
            Self::Implies(_, body) => body.peel_implications(),
            _ => self,
        }
    }
}

/// What an equality between an algebraic `if` and a constructor decides:
/// `if c { A } else { B } == K` with `A` a constructor other than `K`'s
/// holds exactly when `c` is false and `B == K`, and with `B` one other than
/// `K`'s exactly when `c` is true and `A == K`. The condition, its value,
/// and the equality of the branch that remains.
fn decided_algebraic_if(proposition: &Proposition) -> Option<(ConditionTerm, bool, Proposition)> {
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition else {
        return None;
    };
    let (conditional, constructor) = match (&left.node, &right.node) {
        (AlgebraicTermNode::If { .. }, AlgebraicTermNode::Constructor { .. }) => (left, right),
        (AlgebraicTermNode::Constructor { .. }, AlgebraicTermNode::If { .. }) => (right, left),
        _ => return None,
    };
    let (
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        },
        AlgebraicTermNode::Constructor { variant, .. },
    ) = (&conditional.node, &constructor.node)
    else {
        return None;
    };
    let other_constructor = |term: &AlgebraicTerm| matches!(&term.node, AlgebraicTermNode::Constructor { variant: other, .. } if other != variant);
    let (value, selected) = if other_constructor(then_term) {
        (false, else_term)
    } else if other_constructor(else_term) {
        (true, then_term)
    } else {
        return None;
    };
    Some((
        condition.as_ref().clone(),
        value,
        Proposition::Equal(
            Term::Algebraic(selected.as_ref().clone()),
            Term::Algebraic(constructor.clone()),
        ),
    ))
}

/// Recompute the field equalities justified by one exact equality between
/// applications of the same checked algebraic constructor. This single
/// definition is shared by evidence production, index maintenance, and proof
/// checking so none of those layers can disagree about the rule.
pub(crate) fn algebraic_constructor_field_equalities(
    proposition: &Proposition,
) -> Option<Vec<Proposition>> {
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition else {
        return None;
    };
    if left.algebraic_type != right.algebraic_type {
        return None;
    }
    let (
        AlgebraicTermNode::Constructor {
            variant: left_variant,
            ..
        },
        AlgebraicTermNode::Constructor {
            variant: right_variant,
            ..
        },
    ) = (&left.node, &right.node)
    else {
        return None;
    };
    if left_variant != right_variant {
        return None;
    }
    let left_fields = left.checked_constructor_fields()?;
    let right_fields = right.checked_constructor_fields()?;
    left_fields
        .iter()
        .zip(right_fields)
        .map(|(left, right)| match (left, right) {
            (AlgebraicValue::Program(left), AlgebraicValue::Program(right)) => {
                program_value_comparison_proposition(left, ComparisonOperator::Equal, right)
            }
            (AlgebraicValue::Algebraic(left), AlgebraicValue::Algebraic(right)) => {
                Some(Proposition::Equal(
                    Term::Algebraic(left.clone()),
                    Term::Algebraic(right.clone()),
                ))
            }
            _ => None,
        })
        .collect()
}

fn is_algebraic_constructor_conflict(proposition: &Proposition) -> bool {
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition else {
        return false;
    };
    if left.algebraic_type != right.algebraic_type
        || left.checked_constructor_fields().is_none()
        || right.checked_constructor_fields().is_none()
    {
        return false;
    }
    matches!(
        (&left.node, &right.node),
        (
            AlgebraicTermNode::Constructor { variant: left, .. },
            AlgebraicTermNode::Constructor { variant: right, .. }
        ) if left != right
    )
}

impl PureFactContext {
    #[cfg(test)]
    pub(crate) fn reset_bitvector_equality_index_fact_visits() {
        BITVECTOR_EQUALITY_INDEX_FACT_VISITS.with(|visits| visits.set(0));
    }

    #[cfg(test)]
    pub(crate) fn bitvector_equality_index_fact_visits() -> usize {
        BITVECTOR_EQUALITY_INDEX_FACT_VISITS.with(Cell::get)
    }

    /// How many condition facts `exact_signed_constant` has examined on this
    /// thread since the last reset.
    #[cfg(test)]
    pub(crate) fn exact_constant_fact_visits() -> usize {
        EXACT_CONSTANT_FACT_VISITS.with(Cell::get)
    }

    /// How many condition facts the condition-fact queries have examined on
    /// this thread since the last reset.
    #[cfg(test)]
    pub(crate) fn condition_fact_visits() -> usize {
        CONDITION_FACT_VISITS.with(Cell::get)
    }

    #[cfg(test)]
    pub(crate) fn reset_condition_fact_visits() {
        CONDITION_FACT_VISITS.with(|visits| visits.set(0));
    }

    #[cfg(test)]
    pub(crate) fn reset_exact_constant_fact_visits() {
        EXACT_CONSTANT_FACT_VISITS.with(|visits| visits.set(0));
    }

    fn fingerprint<T: std::hash::Hash>(tag: u64, value: &T) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hasher::write_u64(&mut hasher, tag);
        std::hash::Hash::hash(value, &mut hasher);
        std::hash::Hasher::finish(&hasher)
    }

    fn recompute_content_fingerprint(&mut self) {
        let mut fingerprint = 0;
        for fact in self.condition_facts.scan_for_upkeep() {
            fingerprint ^= Self::fingerprint(1, &fact);
        }
        for fact in self.prop_facts.scan_for_upkeep() {
            fingerprint ^= Self::fingerprint(2, fact);
        }
        for (variable, definitions) in self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .iter()
        {
            for (key, (value, _)) in definitions.iter() {
                fingerprint ^= Self::typed_pointer_read_fingerprint(*variable, key, value);
            }
        }
        for resources in self.resource_compositions.scan_for_upkeep() {
            fingerprint ^= Self::fingerprint(3, resources);
        }
        if let Some(owners) = &self.store_owners {
            fingerprint ^= Self::fingerprint(5, owners);
        }
        fingerprint ^= self.reasoning_policy.fingerprint();
        self.content_fingerprint = fingerprint;
    }

    /// [`Self::adjust_signed_order_bound_spelled`] for the fact, and for a native 8- or
    /// 16-bit comparison also for the `int32` comparison of its widenings,
    /// the same fact (rule K8), which the index reads.
    fn adjust_signed_order_bound(&mut self, condition: &ConditionTerm, value: bool) {
        self.adjust_signed_order_bound_spelled(condition, value);
        if let Some(widened) =
            crate::kernel::machine_integer::comparison::narrow_fact_widening(condition)
        {
            self.adjust_signed_order_bound_spelled(&widened, value);
        }
    }

    fn adjust_signed_order_bound_spelled(&mut self, condition: &ConditionTerm, value: bool) {
        self.checked_order_bounds.adjust(condition, value);
        self.order_facts_by_lower.adjust(condition, value);
        self.signed_variable_chains.adjust(condition, value);
        let Some(view) = retained_order_bounds::order_view(condition, value) else {
            return;
        };
        let index = match view.format {
            MachineIntegerType::Int32 => &mut self.signed_order_bounds,
            MachineIntegerType::UInt32 => &mut self.uint32_order_bounds,
            MachineIntegerType::Int64 => &mut self.int64_signed_order_bounds,
            MachineIntegerType::UInt64 => &mut self.uint64_order_bounds,
            _ => return,
        };
        index.adjust(&view, &Proposition::condition_is(condition.clone(), value));
        let kind = match view.format {
            MachineIntegerType::UInt64 => 0,
            MachineIntegerType::Int64 => 1,
            _ => return,
        };
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let strict = view.relation == super::machine_integer::Relation::Less;
        for (direction, from, to) in [(0, left, right), (1, right, left)] {
            self.wide_order_edges[kind][direction].adjust(view.format, from, to, strict);
        }
    }

    /// The pointer whose null-ness one condition fact decides, as the
    /// non-null-block side of an equality against the null pointer.
    ///
    /// Only an equality against the null pointer itself qualifies. A pointer
    /// already displaced from null is not a null test, and a fact relating
    /// two pointers of the null block says nothing about either being null.
    fn condition_as_null_pointer_fact(condition: &ConditionTerm) -> Option<&Address> {
        let ConditionTerm::AddressEqual(left, right) = condition else {
            return None;
        };
        let null = Address::null();
        match (left.as_ref() == &null, right.as_ref() == &null) {
            (true, false) => Some(right.as_ref()),
            (false, true) => Some(left.as_ref()),
            _ => None,
        }
    }

    /// Files one null-ness fact under its pointer's offset.
    ///
    /// Touches exactly the one offset key the fact names, so a context that
    /// gains a null test pays for that test alone.
    fn adjust_null_pointer_offset(&mut self, condition: &ConditionTerm, value: bool) {
        let Some(pointer) = Self::condition_as_null_pointer_fact(condition) else {
            return;
        };
        let (block, offset) = (pointer.base.clone(), pointer.offset.clone());
        let key = (block, value);
        let blocks = self
            .null_pointer_offsets
            .get(&offset)
            .cloned()
            .unwrap_or_default();
        let blocks = blocks.with_inserted(key, condition.clone());
        self.null_pointer_offsets = if blocks.is_empty() {
            self.null_pointer_offsets.without_key(&offset)
        } else {
            self.null_pointer_offsets.with_inserted(offset, blocks)
        };
    }

    /// Files one exact pointer equality under both
    /// of its sides. Only a *true* equality says two spellings are one
    /// address; a false one is not an alias and never enters the index.
    fn adjust_pointer_address_source(
        &mut self,
        key: ConditionTerm,
        source: &ConditionTerm,
    ) -> Option<ConditionTerm> {
        let sources = self
            .equality_graph
            .admitted
            .pointer_address_sources
            .get(&key)
            .cloned()
            .unwrap_or_default();
        let sources = sources.with_value(source.clone());
        let selected = sources.iter().next().cloned();
        self.equality_graph.admitted.pointer_address_sources = if sources.is_empty() {
            self.equality_graph
                .admitted
                .pointer_address_sources
                .without_key(&key)
        } else {
            self.equality_graph
                .admitted
                .pointer_address_sources
                .with_inserted(key, sources)
        };
        selected
    }

    fn adjust_address_base_alias(&mut self, condition: &ConditionTerm, value: bool) {
        if let Some((pointer, alignment)) = condition.as_pointer_alignment() {
            if value && alignment.is_power_of_two() {
                let key = (pointer.clone(), alignment);
                let sources = self
                    .equality_graph
                    .admitted
                    .pointer_alignment_facts
                    .get(&key)
                    .cloned()
                    .unwrap_or_default();
                let sources = sources.with_value(condition.clone());
                if sources.is_empty() {
                    self.equality_graph
                        .admitted
                        .pointer_alignment_facts
                        .remove(&key);
                } else {
                    self.equality_graph
                        .admitted
                        .pointer_alignment_facts
                        .insert(key, sources);
                }
                self.equality_graph.register_alignment(pointer, alignment);
            }
            return;
        }
        let (left, right) = match condition {
            ConditionTerm::AddressEqual(left, right) => (left.as_ref(), right.as_ref()),
            ConditionTerm::PointerEqual(left, right) => (left.address(), right.address()),
            _ => return,
        };
        if !value || left == right {
            return;
        }
        let key = if left < right {
            ConditionTerm::address_equal(left.clone(), right.clone())
        } else {
            ConditionTerm::address_equal(right.clone(), left.clone())
        };
        let source = self.adjust_pointer_address_source(key.clone(), condition);
        if left.base.is_local_block() || right.base.is_local_block() {
            self.equality_graph.admitted.local_pointer_aliases = if source.is_some() {
                self.equality_graph
                    .admitted
                    .local_pointer_aliases
                    .with_value(key)
            } else {
                self.equality_graph
                    .admitted
                    .local_pointer_aliases
                    .without_value(&key)
            };
        }
        for (key, alias) in [(left, right), (right, left)] {
            let aliases = self
                .equality_graph
                .admitted
                .address_base_aliases
                .get(key)
                .cloned()
                .unwrap_or_default();
            let aliases = if let Some(source) = &source {
                aliases.with_inserted(alias.clone(), source.clone())
            } else {
                aliases.without_key(alias)
            };
            let filed = !aliases.is_empty();
            self.equality_graph.admitted.address_base_aliases = if filed {
                self.equality_graph
                    .admitted
                    .address_base_aliases
                    .with_inserted(key.clone(), aliases)
            } else {
                self.equality_graph
                    .admitted
                    .address_base_aliases
                    .without_key(key)
            };
            let bucket = memory_reasoning::parameter_alias_bucket(key);
            let endpoints = self
                .equality_graph
                .admitted
                .pointer_alias_endpoints_by_object
                .get(&bucket)
                .cloned()
                .unwrap_or_default();
            let endpoints = if filed {
                endpoints.with_value(key.clone())
            } else {
                endpoints.without_value(key)
            };
            self.equality_graph
                .admitted
                .pointer_alias_endpoints_by_object = if endpoints.is_empty() {
                self.equality_graph
                    .admitted
                    .pointer_alias_endpoints_by_object
                    .without_key(&bucket)
            } else {
                self.equality_graph
                    .admitted
                    .pointer_alias_endpoints_by_object
                    .with_inserted(bucket, endpoints)
            };
        }
        self.equality_graph.add_equality(left, right);
    }

    pub(in crate::kernel) fn provenance_equal(&self, left: &Address, right: &Address) -> bool {
        left == right
            || self
                .equality_graph
                .admitted
                .provenance_graph
                .equal(left, right)
            || self.equality_graph.provenance_equal(left, right)
            || crate::kernel::memory_history::pointer_read_provenance_equal(left, right, self)
            || self
                .equality_graph
                .admitted
                .provenance_graph
                .unique_direct_alias(right)
                .is_some_and(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::memory_history::pointer_read_provenance_equal(left, alias, self)
                })
            || self
                .equality_graph
                .admitted
                .provenance_graph
                .unique_direct_alias(left)
                .is_some_and(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::memory_history::pointer_read_provenance_equal(alias, right, self)
                })
    }

    pub(in crate::kernel) fn bounds_owners_equal(&self, a: &Address, b: &Address) -> bool {
        self.equality_graph.admitted.bounds_graph.equal(a, b)
            || self.equality_graph.bounds_owners_equal(a, b)
            || crate::kernel::memory_history::pointer_read_bounds_equal(a, b, self)
            || self
                .equality_graph
                .admitted
                .bounds_graph
                .unique_direct_alias(b)
                .is_some_and(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::memory_history::pointer_read_bounds_equal(a, alias, self)
                })
            || self
                .equality_graph
                .admitted
                .bounds_graph
                .unique_direct_alias(a)
                .is_some_and(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::memory_history::pointer_read_bounds_equal(alias, b, self)
                })
    }

    pub(in crate::kernel) fn pointer_provenance_match(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        // A complete read can carry a pointer copied from a different cell.
        // Compare the producer's entire stored value once; scalar address
        // aliases and partial stores cannot supply its provenance or bounds.
        let stored_value = |value: &Pointer| {
            // A cast or member selection has already chosen its own view.
            // Recover only the untouched opaque value of a complete read.
            if value.bounds_are_known()
                || value.bounds().is_some()
                || value.bounds_owner() != Some(value.provenance())
            {
                return None;
            }
            crate::kernel::memory_history::complete_pointer_read_value(value.provenance(), self)
        };
        pointer_checks::complete_match(
            left,
            right,
            |a, b| self.pointer_provenance_match_without_stored_values(a, b),
            stored_value,
        )
    }

    fn pointer_provenance_match_without_stored_values(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        // Null is one pointer value, with no allocation or selected object.
        // Establishing its zero address therefore does not transfer authority.
        ((left.is_null() || self.pointers_known_equal(left.address(), &Address::null()))
            && (right.is_null() || self.pointers_known_equal(right.address(), &Address::null())))
            || self
                .equality_graph
                .admitted
                .pointer_value_classes
                .equal(left, right)
            || self.equality_graph.knows_condition(
                &ConditionTerm::PointerEqual(Box::new(left.clone()), Box::new(right.clone())),
                true,
            )
            || pointer_checks::origins_match(
                pointer_checks::Origins::native(left),
                pointer_checks::Origins::native(right),
                self,
            )
    }

    fn adjust_pointer_equality(&mut self, proposition: &Proposition) {
        let (left, right) = match proposition {
            Proposition::Equal(
                term_source_0 @ Term::ProgramValue(_),
                term_source_1 @ Term::ProgramValue(_),
            ) if let Some(ProgramValue::Pointer(left)) = term_source_0.program_value_native()
                && let Some(ProgramValue::Pointer(right)) =
                    term_source_1.program_value_native() =>
            {
                (left, right)
            }
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((ConditionTerm::PointerEqual(left, right), _)) =
                    condition_source_0.condition_native() =>
            {
                (left.as_ref(), right.as_ref())
            }
            _ => return,
        };
        let key = (left.clone(), right.clone());
        self.equality_graph.admitted.pointer_equalities = self
            .equality_graph
            .admitted
            .pointer_equalities
            .with_value(key);
        self.equality_graph.admitted.provenance_graph.insert(
            left.provenance(),
            right.provenance(),
            |a, _| a.clone(),
        );
        if left.bounds().is_none()
            && right.bounds().is_none()
            && !left.bounds_are_known()
            && !right.bounds_are_known()
            && let Some((a, b)) = left.bounds_owner().zip(right.bounds_owner())
        {
            self.equality_graph
                .admitted
                .bounds_graph
                .insert(a, b, |a, _| a.clone());
        }
        self.equality_graph.admitted.pointer_value_classes.insert(
            left,
            right,
            super::pointer_provenance::prefer_pointer,
        );
        self.equality_graph.add_pointer_equality(left, right);
    }

    fn adjust_algebraic_graph_equality(&mut self, proposition: &Proposition) {
        let (left, right) = match proposition {
            Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) => (a, b),
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((ConditionTerm::AlgebraicEqual(a, b), _)) =
                    condition_source_0.condition_native() =>
            {
                (a.as_ref(), b.as_ref())
            }
            _ => return,
        };
        if left.algebraic_type != right.algebraic_type
            || !left.is_well_formed()
            || !right.is_well_formed()
        {
            return;
        }
        // Retained explicit edges use stable IDs. Deep model keys never enter
        // the persistent graph or its support-count map.
        let atom = |term: &AlgebraicTerm| {
            SharedPureApplication::intern(
                "equality:algebraic-edge".into(),
                vec![PureFunctionArgument::Algebraic(term.clone())],
            )
        };
        let (left_atom, right_atom) = (atom(left), atom(right));
        let edge = if left_atom <= right_atom {
            (left_atom, right_atom)
        } else {
            (right_atom, left_atom)
        };
        self.equality_graph
            .admitted
            .algebraic_graph_equalities
            .insert(edge, ());
        self.equality_graph.add_algebraic_equality(left, right);
    }

    fn adjust_uint64_graph_equality(&mut self, condition: &ConditionTerm, value: bool) {
        let (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        ) = (condition, value)
        else {
            return;
        };
        let edge = {
            let edge = (
                super::equality_graph::MachineAtom::uint64(crate::kernel::canonical_term(left)),
                super::equality_graph::MachineAtom::uint64(crate::kernel::canonical_term(right)),
            );
            self.equality_graph
                .admitted
                .uint64_input_edges
                .insert(condition.clone(), edge.clone());
            edge
        };
        self.equality_graph
            .admitted
            .uint64_graph_equalities
            .insert(edge, ());
        self.equality_graph.add_uint64_equality(left, right);
    }

    pub(in crate::kernel) fn uint64_values_known_equal(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        self.equality_graph.are_uint64_equal(left, right)
    }

    /// [`Self::adjust_int32_graph_equality_spelled`] for the fact, and for a native 8- or
    /// 16-bit comparison also for the `int32` comparison of its widenings,
    /// the same fact (rule K8), which the index reads.
    fn adjust_int32_graph_equality(&mut self, condition: &ConditionTerm, value: bool) {
        self.adjust_int32_graph_equality_spelled(condition, value);
        if let Some(widened) =
            crate::kernel::machine_integer::comparison::narrow_fact_widening(condition)
        {
            self.adjust_int32_graph_equality_spelled(&widened, value);
        }
    }

    fn adjust_int32_graph_equality_spelled(&mut self, condition: &ConditionTerm, value: bool) {
        if !value {
            return;
        }
        // Preserve the same exact-premise translation as the legacy scalar
        // equality index. Equal byte offsets imply equal int32 element-index
        // residues only when both offsets admit that checked interpretation.
        let derived;
        let (left, right) = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => (
                MachineOperandView::Legacy(left),
                MachineOperandView::Legacy(right),
            ),
            condition if condition.true_pointer_offset_sides().is_some() => {
                let (left, right) = condition.true_pointer_offset_sides().expect("offset view");
                let Some(pair) = shared_element_index_from_offset(left, 4)
                    .zip(shared_element_index_from_offset(right, 4))
                else {
                    return;
                };
                derived = pair;
                (derived.0.operand_view(), derived.1.operand_view())
            }
            _ => return,
        };
        // File exact premises under the canonical edge rather than interning
        // raw MemoryLoad payloads. Raw interning can compare whole states
        // across verification arenas.
        let atom = |view: MachineOperandView<'_>| match view {
            MachineOperandView::Legacy(term) => {
                super::equality_graph::MachineAtom::int32(crate::kernel::canonical_term(term))
            }
            MachineOperandView::Shared(_) => {
                super::equality_graph::MachineAtom::from_operand(MachineIntegerType::Int32, view)
            }
        };
        let edge = (atom(left), atom(right));
        self.equality_graph
            .admitted
            .int32_graph_equalities
            .insert(edge, ());
        self.equality_graph.add_int32_equality_views(left, right);
    }

    /// Diagnostic-only access to already admitted read equalities.
    pub(crate) fn read_equality_checkpoint(&self) -> crate::kernel::ReadEqualityCheckpoint {
        self.equality_graph.read_equality_checkpoint()
    }

    pub(crate) fn read_equalities_since(
        &self,
        checkpoint: &crate::kernel::ReadEqualityCheckpoint,
    ) -> crate::kernel::ReadEqualityDelta {
        self.equality_graph.read_equalities_since(checkpoint)
    }

    /// File the typed producer's checked value against an exact defining
    /// equation already admitted on this path. Plain propositions cannot
    /// create this bridge; the execution fact must carry producer metadata.
    pub(in crate::kernel) fn assume_execution_pure_fact(
        mut self,
        fact: &ExecutionPureFact,
    ) -> Self {
        self = self.assume_shared_proposition(fact.shared_proposition());
        if !fact.is_certified() {
            return self;
        }
        if fact.has_checked_pointer_read() {
            fact.retain_pointer_read_definition(&self);
        }
        let Some(
            binding @ GeneratedLoadBinding::Exact {
                variable,
                pointer: address,
                load: MachineTerm::MemoryLoad(memory, _, kind),
                typed_pointer_value: Some(value),
                ..
            },
        ) = fact.generated_load_binding()
        else {
            return self;
        };
        if Some(*kind) != LoadKind::of_type(ProgramType::Int32Pointer)
            || crate::kernel::registered_load_bytes_for_variable(variable)
                != Some(C_POINTER_BYTE_WIDTH)
            || !generated_load_binding_matches_proposition(binding, fact.proposition())
            || crate::kernel::eval::typed_pointer_read_variable(value) != Some(*variable)
        {
            return self;
        }
        // The exact proposition was admitted above. The retained producer
        // binding supplies the read descriptor independently of its spelling.
        self.file_typed_pointer_read(*variable, memory.shared_memory(), address, value);
        self
    }

    /// Select one unambiguous certified program read retained in this
    /// context. Its immutable pair comes from the retained binding, not the
    /// live naming registry. No definition is published to sibling contexts.
    pub(in crate::kernel) fn retained_pointer_read_application(
        &self,
        value: &Address,
    ) -> Option<Address> {
        let variable = crate::kernel::eval::typed_pointer_read_variable(value)?;
        let definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .get(&variable)?;
        if definitions.len() != 1 {
            return None;
        }
        let ((_, address), (retained, source)) = definitions.iter().next()?;
        (retained == value).then(|| Address::loaded_value(source, address))
    }

    /// Publish a typed read's definition and locally checked source equality.
    /// The graph is part of the trusted kernel. One exact materialization or
    /// separate store edge is checked here;
    /// equality queries never search history.
    /// No proposition or read authority is introduced. Checked unions belong
    /// only to this persistent proof context; definitions are unconditional.
    pub(in crate::kernel) fn register_pointer_read(
        &self,
        value: &Address,
        memory: &SharedMemory,
        address: &Address,
    ) {
        self.equality_graph
            .register_pointer_read_definition(value, memory, address);
        self.register_pointer_read_source(memory, address);
    }

    /// Reconcile a retained, checked pointer read with a cached alias value.
    /// Only spellings in its checked address class are queried in this exact
    /// state. Logical term construction does not perform this cell search.
    pub(in crate::kernel) fn register_checked_pointer_read(
        &self,
        value: &Address,
        memory: &SharedMemory,
        address: &Address,
    ) {
        self.register_pointer_read(value, memory, address);
        self.register_cached_pointer_read_value(memory, address);
    }

    fn register_cached_pointer_read_value(&self, memory: &SharedMemory, address: &Address) {
        let start = crate::kernel::prelude::canonical_load_projection_source(memory, address)
            .unwrap_or_else(|| memory.clone());
        for spelling in self.equality_graph.pointer_spellings(address) {
            if let Some(ProgramValue::Pointer(value)) = start.known_value(&spelling) {
                self.equality_graph.add_checked_pointer_equality(
                    &Pointer::new(Address::loaded_value(memory, address), value.program_type()),
                    &value,
                );
                return;
            }
        }
    }

    /// This rule relates load applications only. An execution value's bridge
    /// remains scoped to its certified binding, including restricted contexts.
    fn register_pointer_read_source(&self, memory: &SharedMemory, address: &Address) {
        if let Some(source) = self.pointer_read_source(memory, address) {
            self.equality_graph.add_checked_pointer_read_equality(
                &Address::loaded_value(memory, address),
                &Address::loaded_value(&source, address),
            );
        }
    }

    pub(in crate::kernel) fn pointer_read_source(
        &self,
        memory: &SharedMemory,
        address: &Address,
    ) -> Option<SharedMemory> {
        // This producer names an LP64 pointer read, whose width is known
        // even when no scalar load was recorded at the same address.
        let bytes = crate::kernel::C_POINTER_BYTE_WIDTH;
        let start = crate::kernel::prelude::canonical_load_projection_source(memory, address)
            .unwrap_or_else(|| memory.clone());
        let derivation = start.derivation()?;
        match derivation.as_ref() {
            MemoryDerivation::CellsSeeded { run, .. } => run.read_source(address, bytes),
            MemoryDerivation::Store {
                base,
                pointer: write,
                value,
            } => {
                // Select over exactly one store. Align to its explicitly
                // named block using established graph equality, then check
                // complete byte separation, or use the selected ownership
                // composition's two disjoint complete cells. This checks one
                // store edge; it never searches older states.
                let read = if write.blocks_proven_distinct(address) {
                    Some(address.clone())
                } else {
                    self.equality_graph.pointer_in_block(address, &write.base)
                };
                let separate = read.is_some_and(|read| {
                    crate::kernel::reasoning::exact_access_byte_overlap(
                        write,
                        value.byte_width(),
                        &read,
                        bytes,
                    ) == Some(crate::kernel::reasoning::AccessByteOverlap::Separate)
                })
                    || crate::kernel::memory_history::indexed_store_byte_separation_evidence(
                        write,
                        value.byte_width(),
                        address,
                        bytes,
                        self,
                    )
                    .is_some();
                separate.then(|| base.clone())
            }
            _ => None,
        }
    }

    fn file_typed_pointer_read(
        &mut self,
        variable: Variable,
        memory: &SharedMemory,
        address: &Address,
        value: &Address,
    ) {
        let key = (memory.arena_id(), address.clone());
        let definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .get(&variable)
            .cloned()
            .unwrap_or_default();
        if definitions.contains_key(&key) {
            return;
        }
        let definitions = definitions.with_inserted(key.clone(), (value.clone(), memory.clone()));
        self.equality_graph.admitted.typed_pointer_read_definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .with_inserted(variable, definitions);
        self.content_fingerprint ^= Self::typed_pointer_read_fingerprint(variable, &key, value);
        self.equality_graph
            .add_equality(value, &Address::loaded_value(memory, address));
        self.register_pointer_read_source(memory, address);
        self.register_cached_pointer_read_value(memory, address);
    }

    fn typed_pointer_read_fingerprint(
        variable: Variable,
        key: &((u32, u32), Address),
        value: &Address,
    ) -> u64 {
        Self::fingerprint(4, &(variable, key, value))
    }

    fn adjust_pointer_offset_alias(&mut self, condition: &ConditionTerm, value: bool) {
        let (left, right) = match condition {
            ConditionTerm::AddressOffsetEqual(left, right) => (left.as_ref(), right.as_ref()),
            ConditionTerm::PointerEqual(left, right) if left.base == right.base => {
                (&left.offset, &right.offset)
            }
            _ => return,
        };
        if !value || left == right {
            return;
        }
        let key = if left < right {
            ConditionTerm::AddressOffsetEqual(Box::new(left.clone()), Box::new(right.clone()))
        } else {
            ConditionTerm::AddressOffsetEqual(Box::new(right.clone()), Box::new(left.clone()))
        };
        let source = self.adjust_pointer_address_source(key, condition);
        let retained = source.is_some();
        for (key, alias) in [(left, right), (right, left)] {
            let aliases = self
                .equality_graph
                .admitted
                .pointer_offset_aliases
                .get(key)
                .cloned()
                .unwrap_or_default();
            let aliases = if retained {
                aliases.with_value(alias.clone())
            } else {
                aliases.without_value(alias)
            };
            let root = crate::kernel::primitives::offset_root_atom(alias);
            let rooted = self
                .equality_graph
                .admitted
                .pointer_offset_aliases_by_root
                .get(&root)
                .cloned()
                .unwrap_or_default();
            let pair = (key.clone(), alias.clone());
            let rooted = if retained {
                rooted.with_value(pair)
            } else {
                rooted.without_value(&pair)
            };
            self.equality_graph.admitted.pointer_offset_aliases_by_root = if rooted.is_empty() {
                self.equality_graph
                    .admitted
                    .pointer_offset_aliases_by_root
                    .without_key(&root)
            } else {
                self.equality_graph
                    .admitted
                    .pointer_offset_aliases_by_root
                    .with_inserted(root, rooted)
            };
            self.equality_graph.admitted.pointer_offset_aliases = if aliases.is_empty() {
                self.equality_graph
                    .admitted
                    .pointer_offset_aliases
                    .without_key(key)
            } else {
                self.equality_graph
                    .admitted
                    .pointer_offset_aliases
                    .with_inserted(key.clone(), aliases)
            };
        }
        self.equality_graph.add_offset_equality(left, right);
    }

    /// The offsets with a same-block exact alias whose root atom is `root`
    /// (`resource_algebra::offset_root_atom`): by symmetry of the stated
    /// equalities, the bases one hop from an address at that root. Keyed by
    /// the root, so the answer costs the equalities naming it.
    pub(in crate::kernel) fn offsets_with_an_alias_at_root(
        &self,
        root: &Option<AddressOffset>,
    ) -> Vec<AddressOffset> {
        self.equality_graph.offsets_with_an_alias_at_root(root)
    }

    /// Whether any exact equality joins two blocks.
    pub(in crate::kernel) fn has_address_base_aliases(&self) -> bool {
        self.equality_graph.has_address_base_aliases()
    }

    pub(crate) fn exact_pointer_offset_aliases(
        &self,
        pointer: &Address,
    ) -> impl Iterator<Item = Address> + '_ {
        self.equality_graph.exact_pointer_offset_aliases(pointer)
    }

    pub(in crate::kernel) fn exact_pointer_offset_alias_count(&self, pointer: &Address) -> usize {
        self.equality_graph
            .exact_pointer_offset_alias_count(pointer)
    }

    /// Re-express one selected address using checked graph equality to a
    /// supplied base. This proposes a spelling, not separation authority;
    /// consumers recheck the full pointer equality and complete byte ranges.
    /// `pointer` spelled in `block` when they are one block or one affine
    /// class of the graph. The shallow half of
    /// [`crate::kernel::reasoning::pointer_in_block_for_memory_resolution`]:
    /// no state comparison. It locates an address and grants no access.
    pub(in crate::kernel) fn pointer_in_block(
        &self,
        pointer: &Address,
        block: &AddressBase,
    ) -> Option<Address> {
        if pointer.base == *block {
            return Some(pointer.clone());
        }
        self.equality_graph.pointer_in_block(pointer, block)
    }

    pub(in crate::kernel) fn pointer_at_known_base(
        &self,
        pointer: &Address,
        base: &Address,
    ) -> Option<Address> {
        self.equality_graph.pointer_at_base(pointer, base)
    }

    /// Retain the supplying native index while aligning one selected address.
    /// The spelling supplies no range bounds or access authority.
    pub(in crate::kernel) fn pointer_at_known_base_with_wide_index(
        &self,
        pointer: &Address,
        base: &Address,
    ) -> Option<Address> {
        self.equality_graph
            .pointer_at_base_with_wide_index(pointer, base)
    }

    /// Re-express a selected field only when the maintained affine classes
    /// give a constant byte displacement. This does not expand producer
    /// expressions or retry symbolic range-bound reasoning.
    pub(in crate::kernel) fn pointer_at_known_constant_base(
        &self,
        pointer: &Address,
        base: &Address,
    ) -> Option<Address> {
        fn constant_spine(pointer: &Address) -> Option<(Address, i64)> {
            let mut offset = &pointer.offset;
            let mut bytes = 0i64;
            while let AddressOffset::Add(left, right) = offset {
                crate::instrumentation::record_deterministic_work(1);
                let (rest, extra) = match (left.as_ref(), right.as_ref()) {
                    (rest, AddressOffset::Constant(extra))
                    | (AddressOffset::Constant(extra), rest) => (rest, extra),
                    _ => break,
                };
                bytes = bytes.checked_add(*extra)?;
                offset = rest;
            }
            // A wholly constant offset is its block's origin displaced by
            // it, as `parent->right` is `parent` plus the field's offset.
            if let AddressOffset::Constant(extra) = offset {
                return Some((
                    Address {
                        base: pointer.base.clone(),
                        offset: AddressOffset::Constant(0),
                    },
                    bytes.checked_add(*extra)?,
                ));
            }
            Some((
                Address {
                    base: pointer.base.clone(),
                    offset: offset.clone(),
                },
                bytes,
            ))
        }
        let (origin, displacement) = constant_spine(pointer)?;
        let (base_origin, base_displacement) = constant_spine(base)?;
        // For residual symbolic arithmetic, consult only recorded affine
        // coordinates. Term registration here would revisit array-index
        // dependencies after the direct membership check already failed.
        if matches!(origin.offset, AddressOffset::Add(..))
            || matches!(base_origin.offset, AddressOffset::Add(..))
        {
            return self.equality_graph.pointer_at_constant_base(pointer, base);
        }
        if self.equality_graph.are_equal(&origin, &base_origin) {
            return Some(Address {
                base: base.base.clone(),
                offset: AddressOffset::add(
                    base.offset.clone(),
                    AddressOffset::Constant(displacement.checked_sub(base_displacement)?),
                ),
            });
        }
        self.equality_graph.pointer_at_constant_base(pointer, base)
    }

    /// The pointers an exact fact proves equal to this one, in the index's
    /// own order. One hop: an alias of an alias is not reported, so the
    /// answer is bounded by the equalities stated about this pointer and no
    /// query walks an equality graph.
    /// The pointers with at least one exact alias, in pointer order.
    pub(crate) fn exactly_aliased_pointers(&self) -> impl ExactSizeIterator<Item = &Address> {
        self.equality_graph.exactly_aliased_pointers()
    }

    pub(crate) fn exact_pointer_aliases(
        &self,
        pointer: &Address,
    ) -> impl Iterator<Item = &Address> {
        self.equality_graph.exact_pointer_aliases(pointer)
    }

    /// The pointers a chain of recorded cross-block equalities joins to
    /// `pointer`. Address-only equalities are edges too, so this proposes
    /// candidates and grants nothing; consumers recheck full equality.
    pub(in crate::kernel) fn pointer_alias_class(&self, pointer: &Address) -> Vec<Address> {
        self.equality_graph.pointer_alias_class(pointer)
    }

    pub(super) fn rebuild_null_pointer_offsets(&mut self) {
        self.null_pointer_offsets = crate::persistent::PersistentMap::default();
        let facts = self
            .condition_facts
            .scan_for_upkeep()
            .map(|(condition, value)| (condition.clone(), *value))
            .collect::<Vec<_>>();
        for (condition, value) in facts {
            self.adjust_null_pointer_offset(&condition, value);
        }
    }

    pub(super) fn separated_anchor_key(
        left: AddressOffset,
        right: AddressOffset,
    ) -> (AddressOffset, AddressOffset) {
        if left <= right {
            (left, right)
        } else {
            (right, left)
        }
    }

    pub(super) fn separated_pointer_key(left: Address, right: Address) -> (Address, Address) {
        if left <= right {
            (left, right)
        } else {
            (right, left)
        }
    }

    /// Index one stated separation by its nonempty anchors. Common-block
    /// anchors also distinguish offsets; different blocks distinguish only
    /// complete pointers. Updates touch just this fact's selected key.
    fn adjust_separated_anchor_offsets(
        &mut self,
        proposition: &Proposition,
        left: &MemoryRange,
        right: &MemoryRange,
    ) {
        let (Some(left_anchor), Some(right_anchor)) =
            (memory_range_anchor(left), memory_range_anchor(right))
        else {
            return;
        };
        if left.base().base != right.base().base {
            let key = Self::separated_pointer_key(
                Address {
                    base: left.base().base.clone(),
                    offset: left_anchor,
                },
                Address {
                    base: right.base().base.clone(),
                    offset: right_anchor,
                },
            );
            let facts = self
                .separated_anchor_pointers
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let facts = facts.with_value(proposition.clone());
            self.separated_anchor_pointers = if facts.is_empty() {
                self.separated_anchor_pointers.without_key(&key)
            } else {
                self.separated_anchor_pointers.with_inserted(key, facts)
            };
            return;
        }
        let key = Self::separated_anchor_key(left_anchor, right_anchor);
        let facts = self
            .separated_anchor_offsets
            .get(&key)
            .cloned()
            .unwrap_or_default();
        let facts = facts.with_value(proposition.clone());
        self.separated_anchor_offsets = if facts.is_empty() {
            self.separated_anchor_offsets.without_key(&key)
        } else {
            self.separated_anchor_offsets.with_inserted(key, facts)
        };
    }

    /// Rebuilds the anchor separation index from the stated memory
    /// separations it mirrors.
    #[cfg(test)]
    pub(super) fn rebuild_separated_anchor_offsets(&mut self) {
        self.separated_anchor_offsets = crate::persistent::PersistentMap::default();
        self.separated_anchor_pointers = crate::persistent::PersistentMap::default();
        let stated = self
            .prop_facts
            .iter()
            .filter_map(|proposition| {
                Self::proposition_memory_separation(proposition)
                    .map(|(left, right)| (proposition.clone(), left, right))
            })
            .collect::<Vec<_>>();
        for (proposition, left, right) in stated {
            self.adjust_separated_anchor_offsets(&proposition, &left, &right);
        }
    }

    pub(super) fn rebuild_signed_order_bounds(&mut self) {
        self.checked_order_bounds = Default::default();
        self.order_facts_by_lower = OrderFactsByLower::default();
        self.signed_order_bounds = Default::default();
        self.int64_signed_order_bounds = Default::default();
        self.uint32_order_bounds = Default::default();
        self.uint64_order_bounds = Default::default();
        self.wide_order_edges = Default::default();
        let facts = self
            .condition_facts
            .scan_for_upkeep()
            .map(|(condition, value)| (condition.clone(), *value))
            .collect::<Vec<_>>();
        for (condition, value) in facts {
            self.adjust_signed_order_bound(&condition, value);
        }
    }

    pub(super) fn rebuild_memory_load_condition_facts(&mut self) {
        self.memory_load_condition_facts = crate::persistent::PersistentMap::default();
        let conditions = self
            .condition_facts
            .scan_for_upkeep()
            .map(|(key, _)| key)
            .cloned()
            .collect::<Vec<_>>();
        for condition in conditions {
            self.adjust_memory_load_condition_index(&condition);
        }
        self.equality_graph.admitted.scalar_evidence_inputs = Default::default();
        self.equality_graph.admitted.scalar_dependencies = Default::default();
        self.equality_graph.admitted.scalar_evidence_keys = Default::default();
        self.equality_graph.admitted.bitvector64_equality_facts =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.wide_load_sources = Default::default();
        self.equality_graph.admitted.wide_constant_sources = Default::default();
        self.equality_graph
            .admitted
            .wide_pointer_alias_endpoints_by_object = crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.exact_constant_equalities =
            crate::persistent::PersistentMap::default();
        let conditions = self.condition_facts.clone();
        for (condition, value) in conditions.scan_for_upkeep() {
            self.adjust_scalar_evidence_input(condition, *value);
            self.adjust_bitvector64_equality(condition, *value);
            self.adjust_exact_constant_equality(condition, *value);
        }
    }

    /// Rebuilds the condition-match indexes from `condition_facts`, for a
    /// context whose condition facts were replaced wholesale.
    ///
    /// The exact pointer-alias indexes are derived from the same facts and
    /// are rebuilt with them: a restricted context must not answer an alias
    /// query from an equality it no longer holds.
    fn rebuild_condition_match_indexes(&mut self) {
        self.equality_graph.admitted.scalar_evidence_inputs = Default::default();
        self.equality_graph.admitted.scalar_dependencies = Default::default();
        self.equality_graph.admitted.scalar_evidence_keys = Default::default();
        let prior_typed_reads = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .clone();
        self.checked_scalar_facts = Default::default();
        self.observation_comparisons = Default::default();
        self.condition_facts_by_sides = crate::persistent::PersistentMap::default();
        self.bool_equation_partners = crate::persistent::PersistentMap::default();
        self.address_offset_equalities_by_shape = crate::persistent::PersistentMap::default();
        self.shared_condition_variables = Default::default();
        self.condition_facts_by_variable = crate::persistent::PersistentMap::default();
        self.state_condition_variable_base = crate::persistent::PersistentMap::default();
        self.state_condition_variable_changes = crate::persistent::PersistentMap::default();
        self.state_condition_variables = std::sync::Arc::new(std::sync::OnceLock::new());
        self.open_condition_facts = crate::persistent::PersistentMap::default();
        self.order_condition_facts = Default::default();
        self.difference_graph.reset();
        self.contradictions.reset();
        self.equality_graph.admitted.pointer_alignment_facts =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.address_base_aliases =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.local_pointer_aliases = Default::default();
        self.equality_graph
            .admitted
            .pointer_alias_endpoints_by_object = crate::persistent::PersistentMap::default();
        self.equality_graph.clear_condition_pointer_facts();
        self.equality_graph.reset_closure();
        self.equality_graph.admitted.algebraic_graph_equalities = Default::default();
        self.equality_graph.admitted.congruence_conditions =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.int32_graph_equalities =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.uint64_graph_equalities =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.uint64_input_edges = Default::default();
        self.equality_graph.admitted.typed_pointer_read_definitions =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.pointer_offset_aliases =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.pointer_offset_aliases_by_root =
            crate::persistent::PersistentMap::default();
        self.equality_graph.admitted.pointer_address_sources = Default::default();
        self.equality_graph.admitted.provenance_graph = Default::default();
        self.equality_graph.admitted.bounds_graph = Default::default();
        self.equality_graph.admitted.pointer_value_classes = Default::default();
        self.equality_graph.admitted.pointer_equalities = Default::default();
        let conditions = self.condition_facts.clone();
        for (condition, value) in conditions.scan_for_upkeep() {
            self.adjust_pointer_class_fact(&Proposition::condition_is(condition.clone(), *value));
            if matches!(condition, ConditionTerm::PointerEqual(..)) {
                self.adjust_pointer_equality(&Proposition::condition_is(condition.clone(), *value));
            }
            self.adjust_scalar_evidence_input(condition, *value);
            self.adjust_condition_variable_index(condition, *value, false);
            self.adjust_condition_side_indexes(condition, *value);
            self.adjust_address_base_alias(condition, *value);
            self.adjust_pointer_offset_alias(condition, *value);
            self.adjust_int32_graph_equality(condition, *value);
            self.adjust_uint64_graph_equality(condition, *value);
            self.adjust_algebraic_graph_equality(&Proposition::condition_is(
                condition.clone(),
                *value,
            ));
            if self.equality_graph.add_condition(condition, *value) {
                self.equality_graph
                    .admitted
                    .congruence_conditions
                    .insert(condition.clone(), *value);
            }
        }
        // Restore typing support by the selected equations' load variables,
        // rather than walking every pointer read in the ambient context.
        for (condition, value) in conditions.scan_for_upkeep() {
            if !*value {
                continue;
            }
            let ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } = condition
            else {
                continue;
            };
            let (MachineTerm::Variable(variable), MachineTerm::MemoryLoad(_, _, _)) =
                (left.as_ref(), right.as_ref())
            else {
                continue;
            };
            let Some(kind) = crate::kernel::registered_load_kind_for_variable(variable) else {
                continue;
            };
            if let Some(definitions) = prior_typed_reads.get(variable) {
                for ((_, address), (pointer_value, memory)) in definitions.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    let definition = ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Variable(*variable)),
                        right: Box::new(MachineTerm::MemoryLoad(
                            ProgramPoint::at(memory),
                            Box::new(address.clone()),
                            kind,
                        )),
                    };
                    if self.condition_facts.get(&definition) == Some(&true) {
                        self.file_typed_pointer_read(*variable, memory, address, pointer_value);
                    }
                }
            }
        }
        // The scalar and condition model fragments above already describe
        // the selected context. Add its proposition model edges directly;
        // do not reconstruct those fragments a second time.
        let propositions = self.prop_facts.clone();
        for proposition in propositions.scan_for_upkeep() {
            self.adjust_algebraic_graph_equality(proposition);
            self.adjust_pointer_class_fact(proposition);
            self.adjust_pointer_equality(proposition);
        }
    }

    /// Files one condition fact under its match key and, when
    /// a side is not an atom, among the open facts of its family.
    fn adjust_condition_match_indexes(&mut self, condition: &ConditionTerm, value: bool) {
        if matches!(condition, ConditionTerm::PointerEqual(..)) {
            self.adjust_pointer_equality(&Proposition::condition_is(condition.clone(), value));
        }
        let proposition = Proposition::condition_is(condition.clone(), value);
        self.adjust_condition_variable_index(condition, value, true);
        self.adjust_condition_side_indexes(condition, value);
        self.adjust_comparison_view(&proposition);
        self.adjust_atomic_connection_fact(&proposition);
    }

    fn adjust_condition_variable_index(
        &mut self,
        condition: &ConditionTerm,
        value: bool,
        entry_charged: bool,
    ) {
        let _index_timing =
            crate::instrumentation::OperationTiming::new("", "", "condition variable indexing");
        // assume_condition charges one unit for filing the context entry,
        // including its first adjacency. A restriction rebuild has no such
        // entry charge. Account for additional variables separately so a
        // wide condition remains charged in proportion to its syntax.
        if !entry_charged {
            crate::instrumentation::record_deterministic_work(1);
        }
        if self.shared_condition_variables.adjust(condition, value) {
            return;
        }
        let mut variables = BTreeSet::new();
        let deferred = super::reasoning::variable_collection::collect_condition_index_variables(
            condition,
            &mut variables,
        );
        if deferred {
            // Extend the last completed index by a deferred delta. Adding a
            // new state fact must not re-index older state facts.
            if let Some(index) = self.state_condition_variables.get() {
                self.state_condition_variable_base = index.clone();
                self.state_condition_variable_changes = crate::persistent::PersistentMap::default();
            }
            self.state_condition_variable_changes = self
                .state_condition_variable_changes
                .with_inserted(condition.clone(), value);
            self.state_condition_variables = std::sync::Arc::new(std::sync::OnceLock::new());
        } else {
            crate::instrumentation::record_deterministic_work(variables.len().saturating_sub(1));
            let indexed = SharedIndexFact::new(condition.clone());
            for variable in variables {
                let facts = self
                    .condition_facts_by_variable
                    .get(&variable)
                    .cloned()
                    .unwrap_or_default();
                let facts = facts.with_inserted(indexed.clone(), value);
                self.condition_facts_by_variable = if facts.is_empty() {
                    self.condition_facts_by_variable.without_key(&variable)
                } else {
                    self.condition_facts_by_variable
                        .with_inserted(variable, facts)
                };
            }
        }
    }

    fn adjust_condition_side_indexes(&mut self, condition: &ConditionTerm, value: bool) {
        self.difference_graph.assume(condition, value);

        self.checked_scalar_facts.adjust(condition, value);
        self.observation_comparisons.adjust(condition, value);
        self.observation_comparisons
            .adjust_native_equality(condition, value);
        self.contradictions.adjust(condition, value);
        if let (ConditionTerm::AddressOffsetEqual(left, right), true) = (condition, value) {
            for shape in [offset_state_shape(left), offset_state_shape(right)] {
                let filed = self
                    .address_offset_equalities_by_shape
                    .get(&shape)
                    .cloned()
                    .unwrap_or_default();
                let filed = filed.with_value(condition.clone());
                self.address_offset_equalities_by_shape = if filed.is_empty() {
                    self.address_offset_equalities_by_shape.without_key(&shape)
                } else {
                    self.address_offset_equalities_by_shape
                        .with_inserted(shape, filed)
                };
            }
        }
        if let ConditionTerm::BoolEqual(left, right) = condition {
            for (operand, partner) in [(left, right), (right, left)] {
                let partners = self
                    .bool_equation_partners
                    .get(operand.as_ref())
                    .cloned()
                    .unwrap_or_default();
                let partners = partners.with_inserted(partner.as_ref().clone(), value);
                self.bool_equation_partners = if partners.is_empty() {
                    self.bool_equation_partners.without_key(operand.as_ref())
                } else {
                    self.bool_equation_partners
                        .with_inserted(operand.as_ref().clone(), partners)
                };
            }
        }
        if retained_order_bounds::order_view(condition, value)
            .is_some_and(|view| view.format == MachineIntegerType::Int32)
        {
            self.order_condition_facts = self
                .order_condition_facts
                .with_inserted(condition.clone(), value);
        }
        if let Some(key) = condition_match_key(condition) {
            let family = key.family();
            let facts = self
                .condition_facts_by_sides
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let facts = facts.with_inserted(condition.clone(), value);
            self.condition_facts_by_sides = if facts.is_empty() {
                self.condition_facts_by_sides.without_key(&key)
            } else {
                self.condition_facts_by_sides.with_inserted(key, facts)
            };
            if condition_has_an_open_side(condition) {
                let facts = self
                    .open_condition_facts
                    .get(&family)
                    .cloned()
                    .unwrap_or_default();
                let facts = facts.with_inserted(condition.clone(), value);
                self.open_condition_facts = if facts.is_empty() {
                    self.open_condition_facts.without_key(&family)
                } else {
                    self.open_condition_facts.with_inserted(family, facts)
                };
            }
        }
    }

    /// Files one true equality under each side it pins to a
    /// constant. The two sides are filed exactly as `exact_signed_constant`
    /// used to read them from a scan: the left side names the right side's
    /// constant, and the right side, unless it is the left side itself,
    /// names the left side's.
    /// [`Self::adjust_exact_constant_equality_spelled`] for the fact, and for a native 8- or
    /// 16-bit comparison also for the `int32` comparison of its widenings,
    /// the same fact (rule K8), which the index reads.
    fn adjust_exact_constant_equality(&mut self, condition: &ConditionTerm, value: bool) {
        self.adjust_exact_constant_equality_spelled(condition, value);
        if let Some(widened) =
            crate::kernel::machine_integer::comparison::narrow_fact_widening(condition)
        {
            self.adjust_exact_constant_equality_spelled(&widened, value);
        }
    }

    fn adjust_exact_constant_equality_spelled(&mut self, condition: &ConditionTerm, value: bool) {
        use crate::kernel::machine_integer::{
            Relation,
            comparison::{comparison_view, structural_native_comparison_view},
        };
        // This index names the written operand, including its exact casts.
        // Value-reading simplifications belong to checking, not source keys.
        let view = if matches!(condition, ConditionTerm::Compare { .. }) {
            comparison_view(condition, value)
        } else {
            structural_native_comparison_view(condition, value)
        };
        let Some(view) = view.filter(|view| {
            view.relation == Relation::Equal
                && matches!(
                    view.format,
                    MachineIntegerType::Int32
                        | MachineIntegerType::UInt32
                        | MachineIntegerType::Int64
                        | MachineIntegerType::UInt64
                )
                // Native uint64 equality is spelled by the int64 bitwise
                // equality constructor. Keep the old native admission set.
                && !(view.format == MachineIntegerType::UInt64
                    && matches!(condition, ConditionTerm::Compare { .. }))
        }) else {
            return;
        };
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let mut previous = None;
        for (term, constant) in [
            (left, exact_equality_constant(right)),
            (right, exact_equality_constant(left)),
        ] {
            let Some(constant) = constant else {
                continue;
            };
            let key = checked_scalar_facts::ScalarOperandKey::new(term);
            if previous.as_ref() == Some(&key) {
                continue;
            }
            previous = Some(key.clone());
            let facts = self
                .equality_graph
                .admitted
                .exact_constant_equalities
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let facts = facts.with_inserted(condition.clone(), constant);
            self.equality_graph.admitted.exact_constant_equalities = if facts.is_empty() {
                self.equality_graph
                    .admitted
                    .exact_constant_equalities
                    .without_key(&key)
            } else {
                self.equality_graph
                    .admitted
                    .exact_constant_equalities
                    .with_inserted(key, facts)
            };
        }
    }

    fn adjust_bitvector64_equality(&mut self, condition: &ConditionTerm, value: bool) {
        let admitted_endpoints = self
            .equality_graph
            .admitted
            .uint64_input_edges
            .get(condition)
            .cloned();
        self.equality_graph.admitted.wide_constant_sources.adjust(
            condition,
            value,
            admitted_endpoints.as_ref(),
        );
        let ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
        else {
            return;
        };
        if !value {
            return;
        }
        for side in [left.as_ref(), right.as_ref()] {
            if let Some((_, pointer, kind)) = load_state_and_pointer(side) {
                let key = (pointer, kind);
                let sources = self
                    .equality_graph
                    .admitted
                    .wide_load_sources
                    .get(&key)
                    .cloned()
                    .unwrap_or_default();
                let sources = sources.with_value(condition.clone());
                if sources.is_empty() {
                    self.equality_graph.admitted.wide_load_sources.remove(&key);
                } else {
                    self.equality_graph
                        .admitted
                        .wide_load_sources
                        .insert(key, sources);
                }
            }
        }
        // A word whose recorded equal names a pointer address is filed by
        // class, so the integer-to-pointer cast finds the fact from an equal
        // word (`pointer_tags::form_of`). Other equalities file nothing.
        for (endpoint, other) in [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ] {
            if mentions_pointer_address(other) {
                self.equality_graph.record_wide_equation_endpoint(endpoint);
            }
        }

        for (endpoint, other) in [
            (left.as_ref(), right.as_ref()),
            (right.as_ref(), left.as_ref()),
        ] {
            let key = checked_scalar_facts::ScalarOperandKey::for_format(
                MachineIntegerType::UInt64,
                MachineOperandView::Legacy(endpoint),
            );
            let neighbors = self
                .equality_graph
                .admitted
                .bitvector64_equality_facts
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let neighbors = neighbors.with_inserted(other.clone(), condition.clone());
            if let Some(pointer) = endpoint.address_pointer() {
                let bucket = memory_reasoning::parameter_alias_bucket(pointer);
                let endpoints = self
                    .equality_graph
                    .admitted
                    .wide_pointer_alias_endpoints_by_object
                    .get(&bucket)
                    .cloned()
                    .unwrap_or_default();
                let endpoints = if neighbors.is_empty() {
                    endpoints.without_value(endpoint)
                } else {
                    endpoints.with_value(endpoint.clone())
                };
                self.equality_graph
                    .admitted
                    .wide_pointer_alias_endpoints_by_object = if endpoints.is_empty() {
                    self.equality_graph
                        .admitted
                        .wide_pointer_alias_endpoints_by_object
                        .without_key(&bucket)
                } else {
                    self.equality_graph
                        .admitted
                        .wide_pointer_alias_endpoints_by_object
                        .with_inserted(bucket, endpoints)
                };
            }
            self.equality_graph.admitted.bitvector64_equality_facts = if neighbors.is_empty() {
                self.equality_graph
                    .admitted
                    .bitvector64_equality_facts
                    .without_key(&key)
            } else {
                self.equality_graph
                    .admitted
                    .bitvector64_equality_facts
                    .with_inserted(key, neighbors)
            };
        }
    }

    /// Exact full-width equality neighbours of this term, with their checked
    /// premise. This indexed query never searches unrelated state facts.
    pub(in crate::kernel) fn exact_uint64_equalities(
        &self,
        term: &MachineTerm,
    ) -> impl Iterator<Item = (&MachineTerm, &ConditionTerm)> {
        self.equality_graph.exact_uint64_equalities(term)
    }

    pub(in crate::kernel) fn exact_uint64_equalities_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> impl Iterator<Item = (&MachineTerm, &ConditionTerm)> {
        self.equality_graph.exact_uint64_equalities_view(term)
    }

    /// A full-width observer result can name the same unchanged cell at a
    /// later state. Inspect only equality neighbors of the queried values;
    /// never search unrelated conditions for a matching load.
    #[cfg(test)]
    pub(in crate::kernel) fn uint64_values_equal_for_range_resolution(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        self.uint64_values_equal_for_range_resolution_views(
            MachineOperandView::Legacy(left),
            MachineOperandView::Legacy(right),
        )
    }

    pub(in crate::kernel) fn uint64_values_equal_for_range_resolution_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> bool {
        let same_load = |a: MachineOperandView<'_>, b: MachineOperandView<'_>| {
            let (Some(a), Some(b)) = (a.read_source(), b.read_source()) else {
                return false;
            };
            let (Some((am, ap, ak)), Some((bm, bp, bk))) =
                (load_state_and_pointer(&a), load_state_and_pointer(&b))
            else {
                return false;
            };
            ak == LoadKind::Bits64
                && bk == ak
                && ap == bp
                && memories_match_for_pointer_load(&am, &bm, &ap)
        };
        let equal = |a: MachineOperandView<'_>, b: MachineOperandView<'_>| {
            a.retain(MachineIntegerType::UInt64) == b.retain(MachineIntegerType::UInt64)
        };
        equal(left, right)
            || self.decide(&wide_index_comparison(CompareRelation::Equal, left, right))
                == Some(true)
            || same_load(left, right)
            || self.exact_uint64_equalities_view(left).any(|(other, _)| {
                crate::instrumentation::record_deterministic_work(1);
                let other = MachineOperandView::Legacy(other);
                equal(other, right) || same_load(other, right)
            })
            || self.exact_uint64_equalities_view(right).any(|(other, _)| {
                crate::instrumentation::record_deterministic_work(1);
                let other = MachineOperandView::Legacy(other);
                equal(other, left) || same_load(other, left)
            })
    }

    /// The terms recorded as 64-bit equal to `term` by one exact fact, each
    /// with the stored fact so a certificate can cite it exactly. Loads may
    /// also match the same pointer in a state whose differing cells are
    /// structurally irrelevant to that pointer; this is an assumption-free
    /// state check, not contextual frame reconstruction.
    pub(in crate::kernel) fn recorded_uint64_equals(
        &self,
        term: &MachineTerm,
    ) -> Vec<(MachineTerm, ConditionTerm)> {
        self.equality_graph.recorded_uint64_equals(term)
    }

    /// [`Self::adjust_scalar_evidence_input_spelled`] for the fact, and for a native 8- or
    /// 16-bit comparison also for the `int32` comparison of its widenings,
    /// the same fact (rule K8), which the index reads.
    fn adjust_scalar_evidence_input(&mut self, condition: &ConditionTerm, value: bool) {
        self.adjust_scalar_evidence_input_spelled(condition, value);
        if let Some(widened) =
            crate::kernel::machine_integer::comparison::narrow_fact_widening(condition)
        {
            self.adjust_scalar_evidence_input_spelled(&widened, value);
        }
    }

    fn adjust_scalar_evidence_input_spelled(&mut self, condition: &ConditionTerm, value: bool) {
        self.equality_graph
            .adjust_scalar_evidence_input(condition, value);
    }

    /// The members of `term`'s recorded-equality class other than `term`:
    /// one walk over the indexed equality graph, bounded by the class.
    #[cfg(test)]
    pub(in crate::kernel) fn recorded_equality_class(
        &self,
        term: &MachineTerm,
    ) -> BTreeSet<MachineTerm> {
        self.equality_graph
            .scalar_evidence_class(term)
            .into_iter()
            .collect()
    }

    pub(in crate::kernel) fn recorded_equality_class_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> Vec<SharedMachineIntegerTerm> {
        self.equality_graph.scalar_evidence_class_view(term)
    }

    /// Files `condition` under each memory load it mentions.
    /// The cost is one walk of the condition and one update per load key.
    fn adjust_memory_load_condition_index(&mut self, condition: &ConditionTerm) {
        let mut keys = BTreeSet::new();
        collect_condition_memory_load_keys(condition, &mut keys);
        for key in keys {
            let bucket = self
                .memory_load_condition_facts
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let bucket = bucket.with_value(condition.clone());
            self.memory_load_condition_facts = if bucket.is_empty() {
                self.memory_load_condition_facts.without_key(&key)
            } else {
                self.memory_load_condition_facts.with_inserted(key, bucket)
            };
        }
    }

    pub(crate) fn exact_memory_load_condition_candidates(
        &self,
        pointer: &Address,
    ) -> impl Iterator<Item = (&ConditionTerm, bool)> {
        let exact_key = (
            pointer.base.clone(),
            memory_blind_pointer_fingerprint(pointer),
        );
        self.memory_load_condition_facts
            .get(&exact_key)
            .into_iter()
            .flat_map(|conditions| conditions.iter())
            .filter_map(|condition| {
                self.condition_facts
                    .get(condition)
                    .copied()
                    .map(|value| (condition, value))
            })
    }

    fn adjust_stated_proposition_index(&mut self, proposition: &Proposition) {
        let index = match &self.stated_proposition_index {
            StatedPropositionIndex::Built(index) => index,
            // A fact the key builder declines by shape never enters the
            // index, so it needs no node (and no copy of a deep chain).
            StatedPropositionIndex::Deferred(_)
                if crate::kernel::proof::proposition_identity_key_declines_shape(proposition) =>
            {
                return;
            }
            StatedPropositionIndex::Deferred(node) => {
                self.stated_proposition_index = StatedPropositionIndex::Deferred(
                    std::sync::Arc::new(DeferredStatedIndexNode {
                        parent: std::sync::Mutex::new(Some(node.clone())),
                        adjustment: Some(crate::kernel::clone_proposition_iteratively(proposition)),
                        built: std::sync::OnceLock::new(),
                    }),
                );
                return;
            }
        };
        let Some(key) = crate::kernel::proof::proposition_identity_key(proposition) else {
            // A checked key walk may stop at an exhausted tactic budget after
            // the source fact map has already changed. Drop the whole derived
            // index in that case: a missing index only loses an optimization,
            // while retaining an old entry could make a removed fact appear
            // available. The next insertion/rebuild repopulates it.
            if crate::instrumentation::deadline_exceeded_with_work(0) {
                self.stated_proposition_index = StatedPropositionIndex::default();
            }
            return;
        };
        let index = adjust_stated_index(index, key, proposition);
        self.stated_proposition_index = StatedPropositionIndex::Built(index);
    }

    fn rebuild_stated_proposition_index(&mut self) {
        let mut index = StatedIndexMap::default();
        let mut add = |proposition: &Proposition| {
            let Some(key) = crate::kernel::proof::proposition_identity_key(proposition) else {
                return;
            };
            index = adjust_stated_index(&index, key, proposition);
        };
        for (condition, value) in self.condition_facts.scan_for_upkeep() {
            add(&Proposition::condition_is(condition.clone(), *value));
        }
        for proposition in self.prop_facts.scan_for_upkeep() {
            add(proposition);
        }
        self.stated_proposition_index = StatedPropositionIndex::Built(index);
    }

    /// Builds a deferred stated-proposition index now, as the first query
    /// would. Tests that measure the query itself call it so the one-time
    /// keying of the facts assumed since the last query is not counted
    /// against the lookup.
    #[cfg(test)]
    pub(crate) fn build_stated_proposition_index(&self) {
        let _ = self.stated_proposition_index();
    }

    /// The stated facts alpha-equal to `goal` can only be those filed under
    /// its identity key: the facts of that bucket. None when the key builder
    /// declines `goal` or the index could not be completed in budget.
    pub(in crate::kernel) fn stated_identity_bucket(
        &self,
        goal: &Proposition,
    ) -> impl Iterator<Item = &Proposition> {
        crate::kernel::proof::proposition_identity_key(goal)
            .and_then(|key| self.stated_proposition_index()?.get(&key))
            .into_iter()
            .flat_map(|bucket| bucket.iter())
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The stated-proposition index, or `None` when a deferred index could
    /// not be completed within the active budget.
    fn stated_proposition_index(&self) -> Option<&StatedIndexMap> {
        match &self.stated_proposition_index {
            StatedPropositionIndex::Built(index) => Some(index),
            StatedPropositionIndex::Deferred(node) => node.force(),
        }
    }

    /// Drops every proposition fact and its indexes, for a restriction about
    /// to replace the condition indexes and refile the selected facts.
    pub(super) fn clear_proposition_facts(&mut self) {
        self.prop_facts = Default::default();
        self.exact_propagation = Default::default();
        self.comparison_views = Default::default();
        self.equality_graph.clear_proposition_pointer_facts();
        self.execution_fact_projection = self
            .execution_fact_projection
            .iter()
            .filter(|(key, _)| matches!(key, ContextFactKey::Condition(_)))
            .map(|(key, fact)| (key.clone(), fact.clone()))
            .collect();
        self.rebuild_atomic_connection_facts();
        self.rebuild_stated_proposition_index();
        self.disjunction_facts = crate::kernel::fact_collections::ScanSet::default();
        self.equality_graph
            .admitted
            .algebraic_constructor_field_equalities = crate::persistent::PersistentMap::default();
        self.algebraic_constructor_conflicts = crate::persistent::PersistentMap::default();
        self.algebraic_variable_constructors = crate::persistent::PersistentMap::default();
        self.algebraic_variable_variant_evidence = crate::persistent::PersistentMap::default();
        self.resource_compositions = Default::default();
        self.store_owners = None;
        self.composition_members = Default::default();
        self.composition_object_resources = Default::default();
        self.memory_read_defined_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_object_facts = crate::persistent::PersistentMap::default();
        self.memory_loadable_shape_facts = crate::persistent::PersistentMap::default();
        self.explicit_memory_boundaries = Default::default();
        self.memory_separation_facts = crate::persistent::PersistentMap::default();
        self.resource_contains_facts = crate::persistent::PersistentMap::default();
        self.memory_effect_facts = crate::persistent::PersistentMap::default();
        self.nonmemory_separation_facts = std::sync::Arc::new(Vec::new());
        self.nonmemory_separations_by_side = crate::persistent::PersistentMap::default();
        self.resource_containers = crate::persistent::PersistentMap::default();
        self.memory_containers = crate::persistent::PersistentMap::default();
        self.separation_facts = crate::kernel::fact_collections::ScanSet::default();
        self.separation_facts_by_block = crate::persistent::PersistentMap::default();
        self.wide_separation_facts_by_block = crate::persistent::PersistentMap::default();
        self.separated_address_classes = Default::default();
        self.separated_anchor_offsets = crate::persistent::PersistentMap::default();
        self.separated_anchor_pointers = crate::persistent::PersistentMap::default();
        self.recompute_content_fingerprint();
    }

    fn adjust_pointer_class_fact(&mut self, proposition: &Proposition) {
        if !(matches!(
            proposition,
            Proposition::Equal(..)
                | Proposition::Predicate { .. }
                | Proposition::ResourceSeparate { .. }
        ) || matches!(&proposition, condition_source @ Proposition::ConditionIs(_, true)
                if matches!(condition_source.condition_native(), Some((ConditionTerm::AlgebraicEqual(..) | ConditionTerm::PointerEqual(..), _)))))
        {
            return;
        }
        let key = match proposition {
            Proposition::ConditionIs(condition, _) => {
                ContextFactKey::Condition((condition.clone()).native_compat().clone())
            }
            _ => ContextFactKey::Proposition(proposition.clone()),
        };
        if let Some(source) = self.execution_fact_projection.get(&key) {
            self.equality_graph.adjust_pointer_fact(source, true);
        }
    }

    pub(crate) fn function_contract_facts_for(
        &self,
        pointer: &Address,
    ) -> impl Iterator<Item = (String, Proposition)> {
        self.equality_graph.pointer_function_contracts(pointer)
    }

    fn proposition_memory_separation(
        proposition: &Proposition,
    ) -> Option<(MemoryRange, MemoryRange)> {
        proposition
            .memory_separation()
            .map(|(left, right)| (left.clone(), right.clone()))
    }

    fn adjust_memory_loadable_fact(&mut self, proposition: &Proposition) {
        if let Proposition::MemoryReadDefined {
            memory,
            pointer,
            value_type,
            ..
        } = proposition
        {
            let key = (
                crate::kernel::api::canonicalize_pointer_loads(pointer),
                *value_type,
            );
            let facts = self
                .memory_read_defined_facts
                .get(&key)
                .cloned()
                .unwrap_or_default();
            // The evaluator asks about validity of a memory view. The exact
            // fact store separately retains the observation's point.
            let validity = Proposition::MemoryReadDefined {
                at: None,
                memory: memory.clone(),
                pointer: pointer.clone(),
                value_type: *value_type,
            };
            let sources = facts
                .get(&validity)
                .cloned()
                .unwrap_or_default()
                .with_value(proposition.clone());
            self.memory_read_defined_facts = self
                .memory_read_defined_facts
                .with_inserted(key, facts.with_inserted(validity, sources));
            return;
        }
        let Proposition::MemoryLoadable { base, .. } = proposition else {
            return;
        };
        let object = base.object_identity();
        let object_facts = self
            .memory_loadable_object_facts
            .get(&object)
            .cloned()
            .unwrap_or_default();
        let object_facts = object_facts.with_value(proposition.clone());
        self.memory_loadable_object_facts = if object_facts.is_empty() {
            self.memory_loadable_object_facts.without_key(&object)
        } else {
            self.memory_loadable_object_facts
                .with_inserted(object, object_facts)
        };

        // Persistent, so a context forked from this one shares every block's
        // facts and an insertion copies only the path to its own block.
        let block_facts = self
            .memory_loadable_facts
            .get(&base.base)
            .cloned()
            .unwrap_or_default();
        let block_facts = block_facts.with_value(proposition.clone());
        self.memory_loadable_facts = if block_facts.is_empty() {
            self.memory_loadable_facts.without_key(&base.base)
        } else {
            self.memory_loadable_facts
                .with_inserted(base.base.clone(), block_facts)
        };

        let fingerprint = memory_blind_pointer_fingerprint(base);
        let block_shapes = self
            .memory_loadable_shape_facts
            .get(&base.base)
            .cloned()
            .unwrap_or_default();
        let shape_facts = block_shapes.get(&fingerprint).cloned().unwrap_or_default();
        let shape_facts = shape_facts.with_value(proposition.clone());
        let block_shapes = if shape_facts.is_empty() {
            block_shapes.without_key(&fingerprint)
        } else {
            block_shapes.with_inserted(fingerprint, shape_facts)
        };
        self.memory_loadable_shape_facts = if block_shapes.is_empty() {
            self.memory_loadable_shape_facts.without_key(&base.base)
        } else {
            self.memory_loadable_shape_facts
                .with_inserted(base.base.clone(), block_shapes)
        };
    }

    fn adjust_algebraic_constructor_field_equalities(&mut self, proposition: &Proposition) {
        let Some(fields) = algebraic_constructor_field_equalities(proposition) else {
            return;
        };
        for (field_index, field) in fields.into_iter().enumerate() {
            let source = (proposition.clone(), field_index);
            let mut sources = self
                .equality_graph
                .admitted
                .algebraic_constructor_field_equalities
                .get(&field)
                .cloned()
                .unwrap_or_default();
            sources = sources.with_inserted(source, ());

            self.equality_graph
                .admitted
                .algebraic_constructor_field_equalities = if sources.is_empty() {
                self.equality_graph
                    .admitted
                    .algebraic_constructor_field_equalities
                    .without_key(&field)
            } else {
                self.equality_graph
                    .admitted
                    .algebraic_constructor_field_equalities
                    .with_inserted(field, sources)
            };
        }
    }

    fn adjust_algebraic_constructor_conflict(&mut self, proposition: &Proposition) {
        if !is_algebraic_constructor_conflict(proposition) {
            return;
        }
        self.algebraic_constructor_conflicts = self
            .algebraic_constructor_conflicts
            .with_inserted(proposition.clone(), ());
    }

    fn adjust_algebraic_variable_constructor(&mut self, proposition: &Proposition) {
        let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition else {
            return;
        };
        let (variable, constructor) = match (&left.node, &right.node) {
            (AlgebraicTermNode::Variable(variable), AlgebraicTermNode::Constructor { .. }) => {
                (*variable, right)
            }
            (AlgebraicTermNode::Constructor { .. }, AlgebraicTermNode::Variable(variable)) => {
                (*variable, left)
            }
            _ => return,
        };
        if left.algebraic_type != right.algebraic_type
            || !left.is_well_formed()
            || !right.is_well_formed()
        {
            return;
        }
        let entries = self
            .algebraic_variable_constructors
            .get(&variable)
            .cloned()
            .unwrap_or_default();
        let entries = entries.with_inserted(proposition.clone(), constructor.clone());
        self.algebraic_variable_constructors = if entries.is_empty() {
            self.algebraic_variable_constructors.without_key(&variable)
        } else {
            self.algebraic_variable_constructors
                .with_inserted(variable, entries)
        };
    }

    /// The variant a premise rules out or witnesses for one symbolic
    /// algebraic value, with the scrutinee it speaks about.
    ///
    /// Only the two shapes arm selection can act on are recognized: a
    /// disequality against a field-free constructor, which rules that variant
    /// out, and an existential equality against a constructor, which witnesses
    /// it. Anything else indexes nothing.
    fn proposition_variant_evidence(
        proposition: &Proposition,
    ) -> Option<(Variable, AlgebraicVariantEvidence)> {
        fn scrutinee_and_constructor(
            proposition: &Proposition,
            bound: &BTreeSet<Variable>,
        ) -> Option<(Variable, String, usize)> {
            let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = proposition
            else {
                return None;
            };
            if left.algebraic_type != right.algebraic_type
                || !left.is_well_formed()
                || !right.is_well_formed()
            {
                return None;
            }
            let (variable, constructor) = match (&left.node, &right.node) {
                (AlgebraicTermNode::Variable(variable), AlgebraicTermNode::Constructor { .. }) => {
                    (*variable, right)
                }
                (AlgebraicTermNode::Constructor { .. }, AlgebraicTermNode::Variable(variable)) => {
                    (*variable, left)
                }
                _ => return None,
            };
            if bound.contains(&variable) {
                return None;
            }
            let AlgebraicTermNode::Constructor { variant, fields } = &constructor.node else {
                return None;
            };
            Some((variable, variant.clone(), fields.len()))
        }

        match proposition {
            Proposition::Not(body) => {
                let (variable, variant, arity) = scrutinee_and_constructor(body, &BTreeSet::new())?;
                // `model != Some(3)` leaves `Some` possible; only a field-free
                // constructor names the whole variant.
                (arity == 0).then_some((
                    variable,
                    AlgebraicVariantEvidence {
                        kind: AlgebraicVariantEvidenceKind::Excluded,
                        variant,
                    },
                ))
            }
            Proposition::Exists { .. } => {
                let mut bound = BTreeSet::new();
                let mut body = proposition;
                while let Proposition::Exists {
                    var, body: inner, ..
                } = body
                {
                    bound.insert(*var);
                    body = inner;
                }
                let (variable, variant, _) = scrutinee_and_constructor(body, &bound)?;
                Some((
                    variable,
                    AlgebraicVariantEvidence {
                        kind: AlgebraicVariantEvidenceKind::Witnessed,
                        variant,
                    },
                ))
            }
            _ => None,
        }
    }

    fn adjust_algebraic_variable_variant_evidence(&mut self, proposition: &Proposition) {
        let Some((variable, evidence)) = Self::proposition_variant_evidence(proposition) else {
            return;
        };
        let entries = self
            .algebraic_variable_variant_evidence
            .get(&variable)
            .cloned()
            .unwrap_or_default();
        let entries = entries.with_inserted(proposition.clone(), evidence);
        self.algebraic_variable_variant_evidence = if entries.is_empty() {
            self.algebraic_variable_variant_evidence
                .without_key(&variable)
        } else {
            self.algebraic_variable_variant_evidence
                .with_inserted(variable, entries)
        };
    }

    /// Every premise of this context that rules out or witnesses a variant of
    /// `variable`, with the premise itself so a selection can cite it.
    pub(in crate::kernel) fn algebraic_variant_evidence(
        &self,
        variable: Variable,
    ) -> impl Iterator<Item = (&Proposition, &AlgebraicVariantEvidence)> {
        crate::instrumentation::record_deterministic_work(1);
        self.algebraic_variable_variant_evidence
            .get(&variable)
            .into_iter()
            .flat_map(crate::persistent::PersistentMap::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Whether these facts give `value` a constructor.
    pub(crate) fn knows_algebraic_constructor(&self, value: &AlgebraicTerm) -> bool {
        self.known_algebraic_constructor(value).is_some()
    }

    /// The constructor a fact equates algebraic variable `variable` to.
    pub(in crate::kernel) fn variable_algebraic_constructor(
        &self,
        variable: Variable,
    ) -> Option<AlgebraicTerm> {
        let (premise, constructor) = self
            .algebraic_variable_constructors
            .get(&variable)?
            .iter()
            .next()
            .map(|(premise, constructor)| (premise.clone(), constructor.clone()))?;
        record_consulted_premises(self, &premise);
        Some(constructor)
    }

    /// Whether a fact equates some algebraic variable to a constructor.
    pub(crate) fn has_algebraic_constructor_facts(&self) -> bool {
        !self.algebraic_variable_constructors.is_empty()
    }

    pub(crate) fn known_algebraic_constructor(
        &self,
        value: &AlgebraicTerm,
    ) -> Option<AlgebraicTerm> {
        match &value.node {
            AlgebraicTermNode::Constructor { .. } => value.is_well_formed().then(|| value.clone()),
            // A constructor stated for the variable itself comes first. On an
            // infeasible path the variable's class can join two constructors
            // (a matched `Left` arm and a derived `Top`), and the class keeps
            // only the first witness it saw; the stated one is what the proof
            // is reasoning about.
            AlgebraicTermNode::Variable(variable)
                if let Some((premise, constructor)) = self
                    .algebraic_variable_constructors
                    .get(variable)
                    .and_then(|constructors| {
                        constructors
                            .iter()
                            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                            .find(|(_, constructor)| {
                                constructor.algebraic_type == value.algebraic_type
                            })
                    }) =>
            {
                record_consulted_premises(self, premise);
                Some(constructor.clone())
            }
            _ => {
                let constructor = self.equality_graph.known_algebraic_constructor(value)?;
                record_consulted_premises(
                    self,
                    &Proposition::Equal(
                        Term::Algebraic(value.clone()),
                        Term::Algebraic(constructor.clone()),
                    ),
                );
                Some(constructor)
            }
        }
    }

    pub(crate) fn algebraic_constructor_field_sources(
        &self,
        field: &Proposition,
    ) -> impl Iterator<Item = &(Proposition, usize)> {
        self.equality_graph
            .algebraic_constructor_field_sources(field)
    }

    /// Test census of the loadable facts whose base is in `block`.
    #[cfg(test)]
    pub(crate) fn memory_loadable_candidates(
        &self,
        block: &AddressBase,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_facts
            .get(block)
            .into_iter()
            .flat_map(|facts| facts.iter())
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Return at most one fact per structural or indexed address shape.
    /// Ambiguous buckets and other alias spellings require premise search.
    /// A singleton selected source may be checked across block spellings.
    pub(crate) fn memory_loadable_candidates_for_base(
        &self,
        base: &Address,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_candidates_for_base_with_aliases(base, true, None)
    }

    pub(crate) fn memory_loadable_exact_candidates_for_base(
        &self,
        base: &Address,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_candidates_for_base_with_aliases(base, false, None)
    }

    /// Enumerating an ambiguous address bucket is premise search. The checker
    /// can instead receive one explicitly selected source view.
    pub(crate) fn search_memory_loadable_candidates_for_base(
        &self,
        permission: crate::SearchPermission,
        base: &Address,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_candidates_for_base_with_aliases(base, true, Some(permission))
    }

    fn memory_loadable_candidates_for_base_with_aliases(
        &self,
        base: &Address,
        include_other_spellings: bool,
        permission: Option<crate::SearchPermission>,
    ) -> impl Iterator<Item = &Proposition> {
        crate::instrumentation::record_deterministic_work(1);
        let search = permission.is_some();
        let exact = self
            .memory_loadable_shape_facts
            .get(&base.base)
            .and_then(|shapes| shapes.get(&memory_blind_pointer_fingerprint(base)))
            .filter(|facts| search || facts.len() == 1)
            .into_iter()
            .flat_map(|facts| facts.iter());
        // Do not even prepare an alias class when the exact address answers.
        let related =
            std::iter::once_with(move || self.memory_loadable_related_candidates(base, permission))
                .take(usize::from(
                    include_other_spellings && !self.memory_loadable_facts.is_empty(),
                ))
                .flatten();
        exact
            .chain(related)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .filter(move |fact| match fact {
                Proposition::MemoryLoadable { base: source, .. } => {
                    !base.blocks_proven_distinct(source)
                }
                _ => false,
            })
    }

    /// Class enumeration is premise selection, not part of checked lookup.
    fn memory_loadable_aliases_for_search(
        &self,
        _permission: crate::SearchPermission,
        base: &Address,
    ) -> impl Iterator<Item = Address> {
        self.exact_pointer_aliases(base)
            .cloned()
            .chain(self.equality_graph.pointer_spellings(base))
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    fn memory_loadable_related_candidates(
        &self,
        base: &Address,
        permission: Option<crate::SearchPermission>,
    ) -> impl Iterator<Item = &Proposition> {
        let search = permission.is_some();
        // Structural and maintained class coordinates select keys, never all
        // class members or ranges sharing a block. The exact key was already
        // visited by the caller. Only a planner can append other spellings.
        let mut anchors = vec![Address {
            base: base.base.clone(),
            offset: AddressOffset::Constant(0),
        }];
        let mut offsets = vec![&base.offset];
        while let Some(offset) = offsets.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let AddressOffset::Add(left, right) = offset {
                for part in [left.as_ref(), right.as_ref()] {
                    anchors.push(Address {
                        base: base.base.clone(),
                        offset: part.clone(),
                    });
                    offsets.push(part);
                }
            }
        }
        // Two indexed coordinates, independent of the number of spellings:
        // the maintained affine representative and a unique concrete anchor.
        if let Some(coordinate) = self.equality_graph.canonical_pointer(base)
            && let Some(offset) = coordinate.offset.to_offset_term()
        {
            anchors.push(Address {
                base: coordinate.representative.clone(),
                offset: AddressOffset::Constant(0),
            });
            anchors.push(Address {
                base: coordinate.representative,
                offset,
            });
        }
        let storage = self.equality_graph.storage_address(base);
        anchors.push(Address {
            base: storage.base.clone(),
            offset: AddressOffset::Constant(0),
        });
        anchors.push(storage);
        if let Some(permission) = permission {
            anchors.extend(self.memory_loadable_aliases_for_search(permission, base));
        }
        let mut keys =
            BTreeSet::from([(base.base.clone(), memory_blind_pointer_fingerprint(base))]);
        let anchors = anchors
            .into_iter()
            .filter_map(|anchor| {
                crate::instrumentation::record_deterministic_work(1);
                let key = (
                    anchor.base.clone(),
                    memory_blind_pointer_fingerprint(&anchor),
                );
                keys.insert(key.clone()).then_some(key)
            })
            .collect::<Vec<_>>();
        // A selected singleton can cover an address whose structural anchor
        // normalization erased. Cached length avoids an ambient walk.
        let singleton = self
            .memory_loadable_facts
            .get(&base.base)
            .filter(|facts| facts.len() == 1)
            .or_else(|| {
                // An explicitly selected view may use another block's
                // spelling. Cached lengths select it without an alias
                // walk; coverage still checks the two supplied addresses.
                (self.memory_loadable_facts.len() == 1)
                    .then(|| self.memory_loadable_facts.values().next())
                    .flatten()
                    .filter(|facts| facts.len() == 1)
            })
            .and_then(|facts| facts.iter().next())
            .filter(|fact| match fact {
                Proposition::MemoryLoadable { base, .. } => {
                    !keys.contains(&(base.base.clone(), memory_blind_pointer_fingerprint(base)))
                }
                _ => false,
            });
        anchors
            .into_iter()
            .flat_map(move |(block, fingerprint)| {
                crate::instrumentation::record_deterministic_work(1);
                self.memory_loadable_shape_facts
                    .get(&block)
                    .and_then(|shapes| shapes.get(&fingerprint))
                    .filter(|facts| search || facts.len() == 1)
                    .into_iter()
                    .flat_map(|facts| facts.iter())
            })
            .chain(singleton)
    }

    /// The read-defined facts stated at `pointer` for `value_type`, at one
    /// of its exact aliases, or at another spelling in its equality class:
    /// the keys [`Self::has_memory_read_defined_evidence`] looks up.
    pub(crate) fn search_memory_read_defined_candidates(
        &self,
        _permission: crate::SearchPermission,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Vec<&Proposition> {
        let spellings = self.equality_graph.pointer_spellings(pointer);
        std::iter::once(pointer)
            .chain(self.exact_pointer_aliases(pointer))
            .chain(spellings.iter())
            .filter_map(|candidate| {
                crate::instrumentation::record_deterministic_work(1);
                self.memory_read_defined_facts.get(&(
                    crate::kernel::api::canonicalize_pointer_loads(candidate),
                    value_type,
                ))
            })
            .flat_map(|facts| {
                facts
                    .values()
                    .flat_map(crate::persistent::PersistentSet::iter)
            })
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .collect()
    }

    /// The separation facts the prover consults directly for two memory
    /// ranges: those stated between their blocks, and the residue with a
    /// non-memory side. `None` for any other query shape, which the prover
    /// answers by scanning.
    pub(crate) fn resource_separation_candidates(
        &self,
        left: &Resource,
        right: &Resource,
    ) -> Option<Vec<&Proposition>> {
        let (Resource::Memory(left), Resource::Memory(right)) = (left, right) else {
            return None;
        };
        Some(
            self.memory_separation_candidates(&left.base().base, &right.base().base)
                .map(|(proposition, _, _)| proposition)
                .chain(self.nonmemory_separation_facts.iter())
                .collect(),
        )
    }

    /// SymbolicMemory separations selected by the caller's containment blocks.
    /// Callers additionally name pointers whose related roots and affine
    /// block classes a wide side may cover. A translated window may have no
    /// exact alias at its shifted address, but retains its base's block class.
    /// Results retain proposition order, so a `find`
    /// selects the same witness as the full scan.
    pub(in crate::kernel) fn memory_separations_near<'a, 'b>(
        &'a self,
        blocks: impl IntoIterator<Item = &'b AddressBase>,
        wide_pointers: impl IntoIterator<Item = &'b Address>,
    ) -> std::collections::BTreeSet<&'a Proposition> {
        let blocks = blocks.into_iter().cloned().collect::<BTreeSet<_>>();
        let mut candidates = BTreeSet::new();
        let mut visit = |index: &'a crate::persistent::PersistentMap<
            AddressBase,
            crate::persistent::PersistentSet<Proposition>,
        >,
                         block: &AddressBase| {
            crate::instrumentation::record_deterministic_work(1);
            for fact in index
                .get(block)
                .into_iter()
                .flat_map(crate::persistent::PersistentSet::iter)
            {
                crate::instrumentation::record_deterministic_work(1);
                candidates.insert(fact);
            }
        };
        for block in &blocks {
            visit(&self.separation_facts_by_block, block);
        }
        if !self.wide_separation_facts_by_block.is_empty() {
            let mut wide_blocks = blocks;
            for pointer in wide_pointers {
                wide_blocks.extend(self.equality_graph.pointer_class_blocks(&pointer.base));
                wide_blocks.extend(crate::kernel::primitives::related_pointer_root_blocks(
                    pointer, self,
                ));
            }
            for block in wide_blocks {
                visit(&self.wide_separation_facts_by_block, &block);
            }
        }
        candidates
    }

    pub(in crate::kernel) fn memory_loadable_candidates_for_object(
        &self,
        pointer: &Address,
    ) -> impl Iterator<Item = &Proposition> {
        crate::instrumentation::record_deterministic_work(1);
        self.memory_loadable_object_facts
            .get(&pointer.object_identity())
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    fn memory_separation_key(
        left: &AddressBase,
        right: &AddressBase,
    ) -> (AddressBase, AddressBase) {
        if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        }
    }

    /// Files a memory effect fact under both of its memories.
    fn adjust_memory_effect_fact(&mut self, proposition: &Proposition) {
        let (Proposition::MemoryEffectSummary { before, after, .. }
        | Proposition::MemoryMutatesOnly { before, after, .. }
        | Proposition::HeapAllocationFreed { before, after, .. }) = proposition
        else {
            return;
        };
        for memory in [before, after] {
            let summaries = self
                .memory_effect_facts
                .get(memory)
                .cloned()
                .unwrap_or_default();
            let summaries = summaries.with_value(proposition.clone());
            self.memory_effect_facts = if summaries.is_empty() {
                self.memory_effect_facts.without_key(memory)
            } else {
                self.memory_effect_facts
                    .with_inserted(memory.clone(), summaries)
            };
        }
    }

    /// The memory effect facts with `memory` as their `before` or `after`.
    pub(in crate::kernel) fn memory_effect_facts_naming(
        &self,
        memory: &SymbolicMemory,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_effect_facts
            .get(memory)
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Every memory effect fact once, charged one unit per filed entry. A
    /// fact is filed under both of its memories; it is yielded from the
    /// bucket of its `before` memory.
    pub(in crate::kernel) fn memory_effect_fact_propositions(
        &self,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_effect_facts.iter().flat_map(|(memory, facts)| {
            facts
                .iter()
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .filter(move |fact| {
                    matches!(
                        fact,
                        Proposition::MemoryEffectSummary { before, .. }
                        | Proposition::MemoryMutatesOnly { before, .. }
                        | Proposition::HeapAllocationFreed { before, .. }
                            if before == memory
                    )
                })
        })
    }

    /// Files a `ResourceContains` fact under its parent's key.
    fn adjust_resource_contains_fact(&mut self, proposition: &Proposition) {
        let Proposition::ResourceContains { parent, child } = proposition else {
            return;
        };
        match &**child {
            Resource::Memory(range) => {
                self.memory_containers =
                    with_adjusted_member(&self.memory_containers, &range.base().base, proposition);
            }
            child => {
                self.resource_containers =
                    with_adjusted_member(&self.resource_containers, child, proposition);
            }
        }
        let key = ResourceContainsKey::of(parent);
        let facts = self
            .resource_contains_facts
            .get(&key)
            .cloned()
            .unwrap_or_default();
        let facts = facts.with_value(proposition.clone());
        self.resource_contains_facts = if facts.is_empty() {
            self.resource_contains_facts.without_key(&key)
        } else {
            self.resource_contains_facts.with_inserted(key, facts)
        };
    }

    /// The separation facts with a side that may contain `resource`, a
    /// non-memory resource. Containment of a non-memory resource is identity
    /// or a chain of containment facts down to it
    /// (`proves_resource_contains_inner`), so its containers are walked
    /// upward through the facts filed under each child. A memory parent on
    /// the way is contained by range, up to memory resolution: by a stated
    /// separation's memory side filed under a block related to its base
    /// (`memory_separations_near`), or by a non-memory side, which the
    /// residual list holds (`nonmemory_separation_facts`).
    pub(in crate::kernel) fn separations_with_side_containing(
        &self,
        resource: &Resource,
    ) -> BTreeSet<&Proposition> {
        let mut containers = BTreeSet::from([resource]);
        let mut memory_parents = Vec::new();
        let mut pending = vec![resource];
        while let Some(current) = pending.pop() {
            for fact in self
                .resource_containers
                .get(current)
                .into_iter()
                .flat_map(crate::persistent::PersistentSet::iter)
            {
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::ResourceContains { parent, .. } = fact else {
                    continue;
                };
                if let Resource::Memory(range) = &**parent {
                    memory_parents.push(range);
                    continue;
                }
                if containers.insert(parent) {
                    pending.push(parent);
                }
            }
        }
        let mut separations = BTreeSet::new();
        for container in containers {
            crate::instrumentation::record_deterministic_work(1);
            for fact in self
                .nonmemory_separations_by_side
                .get(container)
                .into_iter()
                .flat_map(crate::persistent::PersistentSet::iter)
            {
                crate::instrumentation::record_deterministic_work(1);
                separations.insert(fact);
            }
        }
        if !memory_parents.is_empty() {
            let blocks = memory_parents
                .iter()
                .flat_map(|range| {
                    crate::kernel::primitives::related_pointer_root_blocks(range.base(), self)
                })
                .collect::<BTreeSet<_>>();
            separations.extend(self.memory_separations_near(
                blocks.iter(),
                memory_parents.iter().map(|range| range.base()),
            ));
            separations.extend(self.nonmemory_separation_facts.iter().inspect(|_| {
                crate::instrumentation::record_deterministic_work(1);
            }));
        }
        separations
    }

    /// The `ResourceContains` facts whose parent `current` may contain by
    /// `resource_contains_builtin`: filed under `current` itself, or for a
    /// memory range under its base block and the blocks of the base's exact
    /// aliases.
    pub(super) fn resource_contains_candidates(&self, current: &Resource) -> Vec<&Proposition> {
        let mut keys = vec![ResourceContainsKey::of(current)];
        if let Resource::Memory(range) = current {
            for alias in self.exact_pointer_aliases(range.base()) {
                let key = ResourceContainsKey::Block(alias.base.clone());
                if !keys.contains(&key) {
                    keys.push(key);
                }
            }
        }
        keys.iter()
            .filter_map(|key| self.resource_contains_facts.get(key))
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .collect()
    }

    fn adjust_memory_separation_fact(&mut self, proposition: &Proposition) {
        let Some(pair) = Self::proposition_memory_separation(proposition) else {
            return;
        };
        self.adjust_separated_anchor_offsets(proposition, &pair.0, &pair.1);
        if let (Some(left), Some(right)) =
            (memory_range_anchor(&pair.0), memory_range_anchor(&pair.1))
        {
            self.separated_address_classes.adjust(
                proposition,
                Address {
                    base: pair.0.base().base.clone(),
                    offset: left,
                },
                Address {
                    base: pair.1.base().base.clone(),
                    offset: right,
                },
                &self.equality_graph,
            );
        }
        let key = Self::memory_separation_key(&pair.0.base().base, &pair.1.base().base);
        // Persistent by block pair, so an insertion copies only its own
        // pair's bucket, not every other pair's.
        let mut pairs = self
            .memory_separation_facts
            .get(&key)
            .cloned()
            .unwrap_or_default();
        std::sync::Arc::make_mut(&mut pairs).push((proposition.clone(), pair.0, pair.1));

        self.memory_separation_facts = if pairs.is_empty() {
            self.memory_separation_facts.without_key(&key)
        } else {
            self.memory_separation_facts.with_inserted(key, pairs)
        };
    }

    /// Files a memory separation under each endpoint block,
    /// in the narrow or wide index according to its bounds.
    fn adjust_separation_block_fact(&mut self, proposition: &Proposition) {
        let Some((left, right)) = proposition.memory_separation() else {
            return;
        };
        let index = if left.wide_bounds().is_some() || right.wide_bounds().is_some() {
            &mut self.wide_separation_facts_by_block
        } else {
            &mut self.separation_facts_by_block
        };
        let mut blocks = vec![left.base().base.clone()];
        if right.base().base != left.base().base {
            blocks.push(right.base().base.clone());
        }
        for key in blocks {
            let bucket = index.get(&key).cloned().unwrap_or_default();
            let bucket = bucket.with_value(proposition.clone());
            *index = if bucket.is_empty() {
                index.without_key(&key)
            } else {
                index.with_inserted(key, bucket)
            };
        }
    }

    /// Maintains the residual separation-fact list: `ResourceSeparate`
    /// facts with at least one non-memory side, which the block-pair index
    /// cannot serve but whose containment may entail memory separation.
    fn adjust_nonmemory_separation_fact(&mut self, proposition: &Proposition) {
        self.index_explicit_memory_boundary(proposition);
        let Proposition::ResourceSeparate { left, right } = proposition else {
            return;
        };
        if Self::proposition_memory_separation(proposition).is_some() {
            return;
        }
        for side in [left, right] {
            if !matches!(**side, Resource::Memory(_)) {
                self.nonmemory_separations_by_side =
                    with_adjusted_member(&self.nonmemory_separations_by_side, side, proposition);
            }
        }
        let residuals = std::sync::Arc::make_mut(&mut self.nonmemory_separation_facts);
        if !residuals.contains(proposition) {
            residuals.push(proposition.clone());
        }
    }

    /// Stated separations whose nonempty anchors are exactly these addresses.
    /// Unlike the block-pair bucket, unrelated external parameters cannot be
    /// candidates. Consumers must still check both complete access widths.
    pub(in crate::kernel) fn anchored_memory_separation_candidates(
        &self,
        left: &Address,
        right: &Address,
    ) -> impl Iterator<Item = &Proposition> {
        let left = self.equality_graph.storage_address(left);
        let right = self.equality_graph.storage_address(right);
        let facts = if left.base == right.base {
            self.separated_anchor_offsets
                .get(&Self::separated_anchor_key(left.offset, right.offset))
        } else {
            self.separated_anchor_pointers
                .get(&Self::separated_pointer_key(left, right))
        };
        facts.into_iter().flat_map(|facts| facts.iter())
    }

    /// The stated memory separations between these two blocks, from the
    /// block-pair index. A composition's same-block separations are not
    /// here: they are asked of the composition when a query needs one
    /// ([`Self::composition_separated_members`]).
    pub(super) fn memory_separation_candidates(
        &self,
        left: &AddressBase,
        right: &AddressBase,
    ) -> impl Iterator<Item = (&Proposition, &MemoryRange, &MemoryRange)> + Clone {
        let key = Self::memory_separation_key(left, right);
        self.memory_separation_facts
            .get(&key)
            .map(|pairs| pairs.as_slice())
            .unwrap_or(&[])
            .iter()
            .map(|(proposition, left, right)| (proposition, left, right))
    }

    /// The composition law, asked on demand: the first held composition with
    /// two distinct owned members that it separates, `left` accepting the
    /// first, `right` the second, and `admit` the pair
    /// (`ResourceContext::separated_owned_members`). The members may lie in
    /// different blocks. Each composition asks its members of the two
    /// blocks, so the query costs the members it reads and never their
    /// pairs, and nothing is stated into this context beforehand.
    ///
    /// `left_at` and `right_at` are addresses the two sides are spelled at;
    /// they choose which members are asked first and never change the
    /// answer (`ResourceContext::separated_owned_members`).
    pub(in crate::kernel) fn composition_separated_members<'a>(
        &'a self,
        left_at: &Address,
        right_at: &Address,
        left: impl Fn(&MemoryRange) -> bool,
        right: impl Fn(&MemoryRange) -> bool,
        admit: impl Fn(&MemoryRange, &MemoryRange) -> bool,
    ) -> Option<(&'a ResourceContext, &'a MemoryRange, &'a MemoryRange)> {
        let (left_block, right_block) = (&left_at.base, &right_at.base);
        // A composition holding the pair is listed under each member's
        // block (`CompositionMemberIndex`).
        self.composition_members
            .listed_under([], [left_block, right_block])
            .into_iter()
            .find_map(|resources| {
                resources
                    .separated_owned_members(
                        left_block,
                        right_block,
                        left_at,
                        right_at,
                        self,
                        &left,
                        &right,
                        &admit,
                    )
                    .map(|(left, right)| (resources, left, right))
            })
    }

    /// Separation of an exposed owner and a checked loan-bound projection.
    /// Candidate lookup uses only the queried address keys, and the retained
    /// composition is the authority subsequently checked by memory evidence.
    pub(in crate::kernel) fn borrow_partition_separated_members<'a>(
        &'a self,
        left: &Address,
        right: &Address,
        contains_left: impl Fn(&MemoryRange) -> bool,
        contains_right: impl Fn(&MemoryRange) -> bool,
    ) -> Option<(&'a ResourceContext, &'a MemoryRange, &'a MemoryRange)> {
        for source in self
            .composition_object_resources
            .partition_sources_at(&[left, right])
        {
            if !self.resource_compositions.contains(source) {
                continue;
            }
            for borrowed in [false, true] {
                if let Some((a, b)) = source
                    .partition_memory_member_at(left, borrowed, &contains_left)
                    .zip(source.partition_memory_member_at(right, !borrowed, &contains_right))
                    && !self.memory_ranges_overlap_after_base_equality(a, b)
                {
                    record_implicit_consulted_premises(
                        self,
                        &Proposition::ResourceComposition(source.clone()),
                    );
                    return Some((source, a, b));
                }
            }
        }
        None
    }

    /// Publish the held entry composition's address input once in this
    /// context's lineage. This prepares an index over the explicit input;
    /// subsequent equality facts advance only their own class deltas.
    /// The publication changes no logical facts or resource permissions.
    pub(crate) fn with_prepared_resource_addresses(mut self, resources: &ResourceContext) -> Self {
        let observable = resources.observable_composition();
        observable.synchronize_memory_equalities(&self);
        self.composition_object_resources.admit(&observable);
        self
    }

    fn adjust_comparison_view(&mut self, source: &Proposition) {
        if let Proposition::ConditionIs(condition, truth) = source
            && crate::kernel::machine_integer::comparison::comparison_view(
                condition.native_compat(),
                *truth,
            )
            .is_some()
        {
            // Atomic aliases are maintained by the shared source index.
            return;
        }
        // Only the newly admitted proposition is visited, never the context.
        let Some(view) = observation_comparisons::PropositionKey::for_source(source) else {
            return;
        };
        let sources = self
            .comparison_views
            .get(&view)
            .cloned()
            .unwrap_or_default();
        self.comparison_views
            .insert(view, sources.with_value(source.clone()));
    }

    pub(super) fn insert_proposition_fact(&mut self, proposition: Proposition) {
        self.insert_shared_proposition_fact(std::sync::Arc::new(proposition));
    }

    fn insert_shared_proposition_fact(&mut self, shared: std::sync::Arc<Proposition>) {
        let proposition = shared.as_ref();
        self.execution_variable_ceiling
            .file_proposition(proposition);
        if let Proposition::ResourceComposition(resources) = proposition {
            if !self.resource_compositions.contains(resources) {
                self.resource_compositions =
                    self.resource_compositions.with_value(resources.clone());
                self.composition_members.admit(resources);
                self.composition_object_resources.admit(resources);
                self.composition_object_resources
                    .advance_memory_equalities(self);
                self.content_fingerprint ^= Self::fingerprint(3, &resources);
                self.admit_shared_exact_propagation(shared);
            }
            return;
        }
        if self
            .prop_facts
            .insert(crate::kernel::clone_proposition_iteratively(proposition))
            .is_none()
        {
            self.execution_fact_projection.insert(
                ContextFactKey::Proposition(proposition.clone()),
                std::sync::Arc::new(ExecutionPureFact::from_shared(shared.clone())),
            );
            self.adjust_comparison_view(proposition);
            self.adjust_atomic_connection_fact(proposition);
            self.adjust_stated_proposition_index(proposition);
            if matches!(proposition, Proposition::Or(_, _)) {
                self.disjunction_facts = self
                    .disjunction_facts
                    .with_value(crate::kernel::clone_proposition_iteratively(proposition));
            }
            if matches!(proposition, Proposition::ResourceSeparate { .. }) {
                self.separation_facts = self
                    .separation_facts
                    .with_value(crate::kernel::clone_proposition_iteratively(proposition));
            }
            self.adjust_algebraic_constructor_field_equalities(proposition);
            self.adjust_algebraic_constructor_conflict(proposition);
            self.adjust_algebraic_variable_constructor(proposition);
            self.adjust_algebraic_graph_equality(proposition);
            self.adjust_pointer_equality(proposition);
            self.adjust_algebraic_variable_variant_evidence(proposition);
            self.adjust_memory_loadable_fact(proposition);
            self.adjust_separation_block_fact(proposition);
            self.adjust_memory_separation_fact(proposition);
            self.adjust_nonmemory_separation_fact(proposition);
            self.adjust_resource_contains_fact(proposition);
            self.adjust_memory_effect_fact(proposition);
            self.adjust_pointer_class_fact(proposition);
            self.content_fingerprint ^= Self::fingerprint(2, &proposition);
            self.admit_shared_exact_propagation(shared);
        }
    }

    #[cfg(test)]
    pub(crate) fn disjunction_fact_count(&self) -> usize {
        self.disjunction_facts.len()
    }

    #[cfg(test)]
    pub(super) fn reset_condition_implication_antecedent_checks() {
        CONDITION_IMPLICATION_ANTECEDENT_CHECKS.with(|checks| checks.set(0));
    }

    #[cfg(test)]
    pub(super) fn condition_implication_antecedent_checks() -> usize {
        CONDITION_IMPLICATION_ANTECEDENT_CHECKS.with(Cell::get)
    }

    #[cfg(test)]
    pub(super) fn reset_memory_separation_candidate_checks() {
        MEMORY_SEPARATION_CANDIDATE_CHECKS.with(|checks| checks.set(0));
    }

    #[cfg(test)]
    pub(super) fn memory_separation_candidate_checks() -> usize {
        MEMORY_SEPARATION_CANDIDATE_CHECKS.with(Cell::get)
    }

    #[cfg(test)]
    pub(super) fn reset_memory_separation_recursive_candidate_checks() {
        MEMORY_SEPARATION_RECURSIVE_CANDIDATE_CHECKS.with(|checks| checks.set(0));
    }

    #[cfg(test)]
    pub(super) fn memory_separation_recursive_candidate_checks() -> usize {
        MEMORY_SEPARATION_RECURSIVE_CANDIDATE_CHECKS.with(Cell::get)
    }

    /// Keep repeated decisions over this borrowed fact set under one memo
    /// identity. Recursive memory resolution can ask several alias questions
    /// about the same large context; without an enclosing scope each question
    /// re-hashes the entire context before consulting the decision memo.
    pub(super) fn enter_id_scope(&self) -> PureFactContextIdScope {
        PureFactContextIdScope::enter(self)
    }

    pub fn new() -> Self {
        Self::default()
    }

    /// Whether this context's facts (`pure_facts`) are `other`'s by storage
    /// identity: the two hold one and the same condition and proposition
    /// sets, so every fact of either is exactly a fact of the other. A
    /// `false` says nothing.
    pub(crate) fn holds_the_facts_of(&self, other: &Self) -> bool {
        self.condition_facts
            .shares_root_with(&other.condition_facts)
            && self.prop_facts.ptr_eq(&other.prop_facts)
    }

    #[cfg(test)]
    pub(crate) fn shares_fact_storage_with(&self, other: &Self) -> bool {
        self.condition_facts
            .shares_root_with(&other.condition_facts)
            && self
                .signed_order_bounds
                .shares_root_with(&other.signed_order_bounds)
            && self
                .int64_signed_order_bounds
                .shares_root_with(&other.int64_signed_order_bounds)
            && self
                .uint32_order_bounds
                .shares_root_with(&other.uint32_order_bounds)
            && self
                .uint64_order_bounds
                .shares_root_with(&other.uint64_order_bounds)
            && self
                .memory_load_condition_facts
                .shares_root_with(&other.memory_load_condition_facts)
            && self.prop_facts.ptr_eq(&other.prop_facts)
            && self
                .stated_proposition_index
                .shares_storage_with(&other.stated_proposition_index)
            && self
                .equality_graph
                .admitted
                .algebraic_constructor_field_equalities
                .shares_root_with(
                    &other
                        .equality_graph
                        .admitted
                        .algebraic_constructor_field_equalities,
                )
            && self
                .algebraic_constructor_conflicts
                .shares_root_with(&other.algebraic_constructor_conflicts)
            && self
                .algebraic_variable_constructors
                .shares_root_with(&other.algebraic_variable_constructors)
            && self
                .resource_compositions
                .shares_root_with(&other.resource_compositions)
            && self
                .memory_loadable_facts
                .shares_root_with(&other.memory_loadable_facts)
            && self
                .memory_loadable_object_facts
                .shares_root_with(&other.memory_loadable_object_facts)
            && self
                .memory_loadable_shape_facts
                .shares_root_with(&other.memory_loadable_shape_facts)
            && self
                .memory_separation_facts
                .shares_root_with(&other.memory_separation_facts)
    }

    #[cfg(test)]
    pub(crate) fn memory_separation_candidate_count(
        &self,
        left: &AddressBase,
        right: &AddressBase,
    ) -> usize {
        self.memory_separation_candidates(left, right).count()
    }

    #[cfg(test)]
    pub(crate) fn memory_loadable_candidate_count(&self, block: &AddressBase) -> usize {
        self.memory_loadable_candidates(block).count()
    }

    pub(crate) fn memo_fingerprint(&self) -> u64 {
        self.content_fingerprint
    }

    /// This context with `owner`, the writer's current observable
    /// composition or `None` when it has none to state, as the ownership its
    /// stores are separated by. A store writes only memory its writer owns
    /// now, so a cached cell in a different member of that ownership keeps
    /// its value; compositions stated earlier on the path are not consulted,
    /// which keeps a store's work independent of the path's length.
    pub(in crate::kernel) fn with_store_owner(self, owner: Option<ResourceContext>) -> Self {
        self.with_store_owners(owner.into_iter().collect())
    }

    /// This context with `opened`, a composition the store opened from what
    /// its writer holds now, stated and added to the store's owners. Without
    /// owners (a context no writer stated them in) it is only stated.
    pub(in crate::kernel) fn with_additional_store_owner(self, opened: ResourceContext) -> Self {
        match &self.store_owners {
            Some(owners) => {
                let mut owners = owners.as_ref().clone();
                owners.push(opened);
                self.with_store_owners(owners)
            }
            None => self.assume_proposition(Proposition::ResourceComposition(opened)),
        }
    }

    fn with_store_owners(mut self, owners: Vec<ResourceContext>) -> Self {
        for owner in &owners {
            self = self.assume_proposition(Proposition::ResourceComposition(owner.clone()));
        }
        if let Some(previous) = &self.store_owners {
            self.content_fingerprint ^= Self::fingerprint(5, previous);
        }
        let owners = std::sync::Arc::new(owners);
        self.content_fingerprint ^= Self::fingerprint(5, &owners);
        self.store_owners = Some(owners);
        self
    }

    /// The compositions the writer stated as its store owners, if it did.
    pub(in crate::kernel) fn store_owners(&self) -> Option<&[ResourceContext]> {
        self.store_owners.as_deref().map(Vec::as_slice)
    }

    /// Return required verification conditions even when the input already
    /// proves them. Statement preparation leaves their proofs to its driver;
    /// this policy changes obligations, never the terms being evaluated.
    pub(crate) fn retaining_required_obligations(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::RETAIN_REQUIRED_OBLIGATIONS)
    }

    /// Argument capture retains its domains for explicit theorem evidence.
    /// This is separate from statement obligation presentation: Integer path
    /// guards must not become extra wrappers on unrelated statement goals.
    pub(crate) fn retaining_argument_obligations(self) -> Self {
        self.retaining_required_obligations()
            .with_reasoning_policy(ReasoningPolicy::RETAIN_ARGUMENT_DOMAINS)
    }

    pub(crate) fn retains_argument_obligations(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::RETAIN_ARGUMENT_DOMAINS)
    }

    pub(crate) fn retains_required_obligations(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::RETAIN_REQUIRED_OBLIGATIONS)
    }

    /// Keep contextual loadability consequences as explicit proof obligations
    /// instead of silently discharging them while symbolic execution is being
    /// planned.
    ///
    /// Condition reasoning is unchanged: this flag only controls the
    /// obligation boundary used by the evaluator.
    pub(crate) fn defer_non_exact_loadability_obligations(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::DEFER_NON_EXACT_LOADABILITY_OBLIGATIONS)
    }

    pub(crate) fn should_defer_non_exact_loadability_obligations(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::DEFER_NON_EXACT_LOADABILITY_OBLIGATIONS)
    }

    /// Surface-certificate synthesis uses this only to structurally lower a
    /// candidate form before comparing it with an already-certified
    /// kernel proposition. Ordinary proof checking must not enable it.
    pub(crate) fn allow_symbolic_contract_loads(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::ALLOW_SYMBOLIC_CONTRACT_LOADS)
    }

    pub(crate) fn should_allow_symbolic_contract_loads(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::ALLOW_SYMBOLIC_CONTRACT_LOADS)
    }

    /// Evaluate a contract entry's own resource clauses. Each states what the
    /// opaque bounds of its pointer covers, so it is assumed, not checked;
    /// the entry builder then records the coverage it states.
    pub(crate) fn assume_entry_clause_spans(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::ASSUME_ENTRY_CLAUSE_SPANS)
    }

    pub(crate) fn should_assume_entry_clause_spans(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::ASSUME_ENTRY_CLAUSE_SPANS)
    }

    /// Project a held resource's body using the domains its fold established.
    /// Ordinary entry requirements and new folds keep their domain obligations.
    pub(crate) fn assume_held_resource_domains(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::ASSUME_HELD_RESOURCE_DOMAINS)
    }

    pub(crate) fn should_assume_held_resource_domains(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::ASSUME_HELD_RESOURCE_DOMAINS)
    }

    pub(crate) fn require_owned_expression_loads(mut self) -> Self {
        if self.should_allow_symbolic_contract_loads() {
            self.toggle_reasoning_policy(ReasoningPolicy::ALLOW_SYMBOLIC_CONTRACT_LOADS);
        }
        self.with_reasoning_policy(ReasoningPolicy::REQUIRE_OWNED_EXPRESSION_LOADS)
    }

    /// An empty context with this one's reasoning policy: the context a
    /// fact-free lowering runs in (`kernel::fact_stability`).
    pub(crate) fn without_facts(&self) -> Self {
        let mut empty = Self::new();
        empty.reasoning_policy = self.reasoning_policy;
        empty
    }

    fn with_reasoning_policy(mut self, choice: ReasoningPolicy) -> Self {
        if !self.reasoning_policy.contains(choice) {
            self.toggle_reasoning_policy(choice);
        }
        self
    }

    fn toggle_reasoning_policy(&mut self, choice: ReasoningPolicy) {
        self.reasoning_policy.toggle(choice);
        self.content_fingerprint ^= choice.fingerprint();
    }

    pub(in crate::kernel) fn should_require_owned_expression_loads(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::REQUIRE_OWNED_EXPRESSION_LOADS)
    }

    pub(crate) fn transport_memory_load_condition_facts(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::TRANSPORT_MEMORY_LOAD_CONDITION_FACTS)
    }

    pub(crate) fn should_transport_memory_load_condition_facts(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::TRANSPORT_MEMORY_LOAD_CONDITION_FACTS)
    }

    pub(crate) fn defer_non_exact_condition_reasoning(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::DEFER_NON_EXACT_CONDITION_REASONING)
    }

    pub(super) fn should_defer_non_exact_condition_reasoning(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::DEFER_NON_EXACT_CONDITION_REASONING)
    }

    /// The pure function definitions the kernel evaluates constant
    /// applications by. A context carries one table.
    pub(crate) fn prefer_symbolic_external_loads(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::PREFER_SYMBOLIC_EXTERNAL_LOADS)
    }

    pub(super) fn should_prefer_symbolic_external_loads(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::PREFER_SYMBOLIC_EXTERNAL_LOADS)
    }

    pub(crate) fn force_symbolic_external_loads(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::FORCE_SYMBOLIC_EXTERNAL_LOADS)
    }

    pub(crate) fn should_force_symbolic_external_loads(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::FORCE_SYMBOLIC_EXTERNAL_LOADS)
    }

    pub(crate) fn keep_spec_loads_symbolic(self) -> Self {
        self.with_reasoning_policy(ReasoningPolicy::KEEP_SPEC_LOADS_SYMBOLIC)
    }

    pub(super) fn should_keep_spec_loads_symbolic(&self) -> bool {
        self.reasoning_policy
            .contains(ReasoningPolicy::KEEP_SPEC_LOADS_SYMBOLIC)
    }

    /// What difference logic over this context's condition facts decides
    /// about `condition` (`docs/internals/verification-efficiency.md`), with `extra` facts
    /// assumed on top: a path's facts not yet in the context.
    pub(crate) fn difference_decision(
        &self,
        condition: &ConditionTerm,
        extra: &[(ConditionTerm, bool)],
    ) -> Option<bool> {
        self.fast_leaf_decision(condition, extra).or_else(|| {
            // A 64-bit word equality may relate tagged addresses
            // (`address(p) + tag`): the pointer-tag rules decide it, asking
            // only these fast decisions at their leaves.
            let ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } = condition
            else {
                return None;
            };
            let mut used = crate::kernel::eval::pointer_tags::UsedFacts::fast_only();
            self.decide_pointer_word_equality_citing(left, right, &mut used)
        })
    }

    /// The fast decisions with no search: the difference graph, asked the
    /// question and its canonical form, and the keyed pointer and division
    /// rules.
    pub(in crate::kernel) fn fast_leaf_decision(
        &self,
        condition: &ConditionTerm,
        extra: &[(ConditionTerm, bool)],
    ) -> Option<bool> {
        if matches!(
            condition,
            ConditionTerm::AddressEqual(..) | ConditionTerm::AddressOffsetEqual(..)
        ) && (self
            .equality_graph
            .admitted
            .pointer_address_sources
            .contains_key(condition)
            || self
                .equality_graph
                .admitted
                .pointer_address_sources
                .contains_key(&condition.flipped()))
        {
            return Some(true);
        }
        // Object-class annotations do not change numeric addresses. The
        // typed numeric graph shares those spellings, including disequality.
        if let ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } = condition
            && left.address_pointer().is_some()
            && right.address_pointer().is_some()
        {
            if self.equality_graph.are_uint64_equal(left, right) {
                return Some(true);
            }
            if self.equality_graph.knows_condition(condition, false) {
                return Some(false);
            }
            if self.addresses_separated_by_class(condition) {
                return Some(false);
            }
        }
        let graph = self.difference_graph.graph(|| {
            self.condition_facts
                .scan_for_upkeep()
                .map(|(condition, value)| (condition, *value))
                .collect()
        });
        // A load in the question may be spelled as the load itself where
        // the facts name it by its load variable: its canonical form, equal
        // by definition, is asked too.
        let canonical = || {
            let canonical = crate::kernel::eval::canonical_condition(condition);
            (&canonical != condition).then_some(canonical)
        };
        // A pointer comparison the graph leaves open may still be decided
        // unequal by the keyed null-ness and separation indexes
        // (`decide_pointer_disequality`), which search nothing.
        let pointer_disequality = || match condition {
            ConditionTerm::AddressEqual(..) | ConditionTerm::AddressOffsetEqual(..) => {
                self.decide_pointer_disequality(condition)
            }
            // `left != INT_MIN or right != -1` kept whole as a fact: two
            // keyed lookups (`divide_overflow_excluded_by_disjunction`).
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Divide,
                left,
                right,
            } => self
                .divide_overflow_excluded_by_disjunction(left, right)
                .then_some(false),
            _ => None,
        };
        if extra.is_empty() {
            return graph
                .decide(condition)
                .or_else(|| canonical().and_then(|canonical| graph.decide(&canonical)))
                .or_else(pointer_disequality)
                .or_else(|| aliased_operands(graph, condition));
        }
        let mut graph = graph.clone();
        for (fact, value) in extra {
            graph.assume_condition(fact, *value);
        }
        graph
            .decide(condition)
            .or_else(|| canonical().and_then(|canonical| graph.decide(&canonical)))
            .or_else(pointer_disequality)
            .or_else(|| aliased_operands(&graph, condition))
    }

    pub(crate) fn proves_exact(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        // The read-over-write authority: a read of a stored cell is the
        // value stored there (`eval::read_over_write_value`). Consulted only
        // when the proposition does not hold as written.
        self.proves_exact_unresolved(proposition)
            || crate::kernel::eval::comparison_form(proposition).is_some_and(|resolved| {
                self.proves_exact_unresolved(&resolved)
                    || crate::kernel::proof::fact_reasoning::normalizes_context_free_leaf(&resolved)
            })
    }

    fn proves_exact_unresolved(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        // An exact full-pointer premise directly supplies its numeric
        // equality. Retain the actual source premise for proof reconstruction; this
        // projection never runs in the reverse direction.
        if let Some((
            condition @ (ConditionTerm::AddressEqual(..) | ConditionTerm::AddressOffsetEqual(..)),
            true,
        )) = (proposition).condition_native()
            && let Some(source) = self
                .equality_graph
                .admitted
                .pointer_address_sources
                .get(condition)
                .or_else(|| {
                    self.equality_graph
                        .admitted
                        .pointer_address_sources
                        .get(&condition.flipped())
                })
                .and_then(|sources| sources.iter().next())
        {
            record_implicit_consulted_premises(
                self,
                &Proposition::condition_is(source.clone(), true),
            );
            return true;
        }
        if self.contains_assumed_exact(proposition) {
            record_implicit_consulted_premises(self, proposition);
            return true;
        }
        // Compound comparison identities select a held source, not a newly
        // manufactured alias. Exact membership stays separate.
        if !self.comparison_views.is_empty()
            && matches!(
                proposition,
                Proposition::ResourceContains { .. }
                    | Proposition::ResourceSeparate { .. }
                    | Proposition::Not(_)
                    | Proposition::And(_, _)
                    | Proposition::Or(_, _)
                    | Proposition::Implies(_, _)
                    | Proposition::ForAll { .. }
                    | Proposition::Exists { .. }
            )
            && let Some(source) = self
                .comparison_views
                .get(&observation_comparisons::PropositionKey::new(proposition))
                .and_then(|sources| sources.iter().next())
        {
            record_implicit_consulted_premises(self, source);
            return true;
        }
        false
    }

    /// Exact membership in the explicitly assumed fact set, without builtin
    /// solving or consulted-premise side effects. This is the indexed analogue
    /// of searching an ambient proposition slice for an atomic conjunct.
    pub(crate) fn contains_assumed_exact(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.condition_facts.get(condition.native_compat()) == Some(value)
                    || self.prop_facts.contains(proposition)
            }
            Proposition::And(left, right) => {
                self.contains_assumed_exact(left) && self.contains_assumed_exact(right)
            }
            Proposition::ResourceComposition(resources) => {
                self.resource_compositions.contains(resources)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.condition_facts.get(condition.native_compat()) == Some(&!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            _ => self.prop_facts.contains(proposition),
        }
    }

    /// Semantic availability through the shared scoped equality graph and
    /// indexed stated separation and exact native Integer observations.
    /// Exact membership remains separate for
    /// consulted premises and admission.
    /// This performs no unfolding, implication search, or state transport.
    pub(crate) fn contains_known(&self, proposition: &Proposition) -> bool {
        // An indexed conflict among checked scalar equalities makes this
        // scoped context impossible. Its semantic consequences need no new
        // search or materialized negation; exact membership stays unchanged.
        if self.equality_graph.has_scalar_constant_conflict() {
            return true;
        }
        // Logical structure is handled by the proof rule. Do not repeatedly
        // traverse a whole conjunction while its caller visits its leaves.
        if matches!(proposition, Proposition::And(..) | Proposition::Or(..)) {
            return self.prop_facts.contains(proposition);
        }
        if self.contains_assumed_exact(proposition) {
            return true;
        }
        if matches!(
            proposition,
            Proposition::ForAll { .. } | Proposition::Exists { .. } | Proposition::Implies(..)
        ) && self.contains_proposition_fact(proposition)
        {
            return true;
        }
        match proposition {
            Proposition::MemoryReadDefined {
                memory,
                pointer,
                value_type,
                ..
            } => {
                // Reuse a typed validity fact for this exact view. The fact's
                // point remains distinct in exact membership and in proofs
                // that construct a fact at a specific footprint endpoint.
                // This lookup takes no alias or history steps.
                self.memory_read_defined_facts
                    .get(&(
                        crate::kernel::api::canonicalize_pointer_loads(pointer),
                        *value_type,
                    ))
                    .is_some_and(|facts| {
                        facts.contains_key(&Proposition::MemoryReadDefined {
                            at: None,
                            memory: memory.clone(),
                            pointer: pointer.clone(),
                            value_type: *value_type,
                        })
                    })
            }
            Proposition::Equal(
                term_source_0 @ Term::ProgramValue(_),
                term_source_1 @ Term::ProgramValue(_),
            ) if let Some(ProgramValue::Pointer(left)) = term_source_0.program_value_native()
                && let Some(ProgramValue::Pointer(right)) =
                    term_source_1.program_value_native() =>
            {
                self.equality_graph
                    .admitted
                    .pointer_value_classes
                    .equal(left, right)
                    || (self.provenance_equal(left.provenance(), right.provenance())
                        && left.bounds() == right.bounds()
                        && self.pointers_known_equal(left.address(), right.address()))
            }
            Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) => {
                self.equality_graph.are_algebraic_equal(a, b)
            }
            Proposition::Predicate { .. } => {
                self.equality_graph.knows_pointer_predicate(proposition)
            }
            condition_source_0 @ Proposition::ConditionIs(_, value)
                if let Some((condition @ ConditionTerm::PointerEqual(..), _)) =
                    condition_source_0.condition_native() =>
            {
                self.decide(condition) == Some(*value)
            }
            Proposition::ConditionIs(condition, value) => {
                self.knows_condition_or_stated_separation(condition.native_compat(), *value)
            }
            Proposition::ResourceSeparate { left, right } => {
                let (Resource::Memory(left_range), Resource::Memory(right_range)) =
                    (left.as_ref(), right.as_ref())
                else {
                    return false;
                };
                if self.resource_separation_conflicts_with_equalities(left, right) {
                    return false;
                }
                let Some(source) = self.separated_address_classes.exact_spans(
                    left_range,
                    right_range,
                    &self.equality_graph,
                ) else {
                    return false;
                };
                record_implicit_consulted_premises(self, &source);
                true
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.knows_condition_or_stated_separation(condition.native_compat(), !*value)
                }
                _ => false,
            },
            _ => false,
        }
    }

    fn knows_condition_or_stated_separation(&self, condition: &ConditionTerm, value: bool) -> bool {
        if let Some(source) = self.observation_comparisons.source(condition, value) {
            record_implicit_consulted_premises(self, source);
            return true;
        }
        self.equality_graph.knows_condition(condition, value)
            // A 32-bit order claim in its mirrored direction (`255 >= x` for
            // `x <= 255`): the graph keeps each order condition in the
            // direction it was stated, and a widening's class holds its
            // operand (rule K8, a relation), so the stated direction over
            // the operand answers the mirrored one over the widening. One
            // more lookup.
            || mirrored_order32(condition)
                .is_some_and(|mirrored| self.equality_graph.knows_condition(&mirrored, value))
            // A signedness conversion's sign test is known when its
            // operand's half-range test is, and the reverse
            // (`condition_reasoning::sign_bit`).
            || self
                .sign_bit_equivalent_conditions(condition)
                .into_iter()
                .any(|equivalent| {
                    Self::without_sign_bit_rule(|| {
                        self.equality_graph.knows_condition(&equivalent, value)
                    })
                })
            || (!value && self.addresses_separated_by_class(condition))
            || super::machine_integer::comparison::native_comparison_view(condition, value)
                .is_some_and(|view| {
                    let (read, truth) = view.retained_condition();
                    (read != *condition || truth != value)
                        && self.contains_known(&Proposition::condition_is(read, truth))
                })
    }

    pub(in crate::kernel) fn addresses_separated_by_class(
        &self,
        condition: &ConditionTerm,
    ) -> bool {
        // Preserve the direct anchor lookup. Only an alias-dependent query
        // needs to register a condition application in the shared classes.
        if self.stated_pointer_disequality(condition) == Some(false) {
            return true;
        }
        let Some(source) = self.equality_graph.address_separation_source(condition) else {
            return false;
        };
        record_implicit_consulted_premises(self, &source);
        true
    }

    /// This context extended by `condition == value`, charged one unit of
    /// deterministic work: every fact a context is built from is charged
    /// once, so a caller that rebuilds a context from a growing list per
    /// item shows as quadratic work rather than hiding in wall time.
    pub fn assume_condition(self, condition: ConditionTerm, value: bool) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        self.assume_condition_uncharged(condition, value)
    }

    fn assume_condition_uncharged(self, condition: ConditionTerm, value: bool) -> Self {
        self.assume_condition_with_source(condition, value, None)
    }

    fn assume_condition_with_source(
        self,
        condition: ConditionTerm,
        value: bool,
        source: Option<std::sync::Arc<Proposition>>,
    ) -> Self {
        let (decided, reduced) = if self.condition_facts.get(&condition) == Some(&value) {
            (None, None)
        } else {
            let proposition = Proposition::condition_is(condition.clone(), value);
            let decided = match &condition {
                ConditionTerm::AlgebraicEqual(left, right) if value => {
                    decided_algebraic_if(&Proposition::Equal(
                        Term::Algebraic(left.as_ref().clone()),
                        Term::Algebraic(right.as_ref().clone()),
                    ))
                }
                _ => None,
            };
            (decided, self.reduce_by_decided_conditions(&proposition))
        };
        // An 8- or 16-bit signedness conversion's sign test, which names a
        // cast no plain comparison of its operand does, also files its
        // operand's half-range test, and the reverse
        // (`condition_reasoning::sign_bit`). So does a 32-bit test of σ,
        // the 32-bit sign cast, a node of its own: `u as int32 < 0` files
        // `u > 2^31 - 1`. A 64-bit one needs no filing: both tests compare
        // one word, and a lookup of either finds the other.
        let sign_bit_equivalents = if (condition.names_narrow_signedness_cast()
            || condition.names_sign_cast32())
            && self.condition_facts.get(&condition) != Some(&value)
        {
            self.sign_bit_equivalent_conditions(&condition)
        } else {
            Vec::new()
        };
        // Rule C's probe: only a comparison naming σ of a quotient or
        // remainder (one match on the root and each side) is kept.
        let sign_cast_division = (condition.names_sign_cast_division()
            && self.condition_facts.get(&condition) != Some(&value))
        .then(|| condition.clone());
        let mut next = self.assume_condition_once_shared(condition, value, source);
        if !sign_bit_equivalents.is_empty() {
            next = Self::without_sign_bit_rule(|| {
                sign_bit_equivalents
                    .into_iter()
                    .filter(|equivalent| !matches!(equivalent, ConditionTerm::Constant(_)))
                    .fold(next, |next, equivalent| {
                        next.assume_condition_once(equivalent, value)
                    })
            });
        }
        // Rule C: a comparison naming σ of a quotient or remainder on
        // operands of known sign also files its reading at the other
        // signedness (`condition_reasoning::sign_cast_division`).
        if let Some(probe) = sign_cast_division
            && let Some(reading) = next.sign_cast_division_equivalent(&probe)
            && reading != probe
        {
            next = next.assume_condition_once(reading, value);
        }
        if let Some((condition, value, selected)) = decided {
            next = next.assume_decided_algebraic_if(condition, value, selected);
        }
        if let Some(reduced) = reduced {
            next = next.assume_proposition_uncharged(reduced);
        }
        next
    }

    /// A repeated assumption is either redundant or immediately contradictory.
    /// Keep the first condition entry and all its indexes. Record contradiction
    /// as an ordinary false proposition, so retained premises and reconstruction
    /// preserve it without needing a hidden flag or an index rebuild. The
    /// proposition set is distinct from the condition map: even a prior
    /// `false == false` fact must not be replaced to record falsehood.
    fn restates_condition(&mut self, condition: &ConditionTerm, value: bool) -> bool {
        let Some(known) = self.condition_facts.get(condition).copied() else {
            return false;
        };
        if known != value {
            self.insert_proposition_fact(Proposition::condition_is(
                ConditionTerm::Constant(false),
                true,
            ));
        }
        true
    }

    fn assume_condition_once(self, condition: ConditionTerm, value: bool) -> Self {
        self.assume_condition_once_shared(condition, value, None)
    }

    fn assume_condition_once_shared(
        mut self,
        condition: ConditionTerm,
        value: bool,
        source: Option<std::sync::Arc<Proposition>>,
    ) -> Self {
        // Proof branches frequently restate a path fact (for example while
        // lowering the consequent of an implication). Preserve the shared
        // persistent view on that idempotent insertion: `Arc::make_mut`
        // would otherwise clone the complete fact map and every derived
        // index before discovering that nothing changed.
        if self.restates_condition(&condition, value) {
            return self;
        }
        crate::kernel::eval::check_canonical_at_creation(&condition, value);
        if cfg!(debug_assertions) {
            let widths = &mut self.variable_widths;
            crate::kernel::debug_assert_widths(
                "an assumed condition",
                || match crate::kernel::condition_variable_widths(&condition) {
                    Err(mismatch) => Some(mismatch),
                    Ok(used) => {
                        used.into_iter()
                            .find_map(|(variable, width)| match widths.get(&variable) {
                                Some(&first) if first != width => {
                                    Some(crate::kernel::variable_conflict(first, width))
                                }
                                Some(_) => None,
                                None => {
                                    widths.insert(variable, width);
                                    None
                                }
                            })
                    }
                },
                &condition,
            );
        }
        if let ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation: CompareRelation::Equal,
            left,
            right,
        } = &condition
            && let Some((left, right)) = bitvector_equality_after_additive_cancellation(left, right)
        {
            self = self.assume_condition_uncharged(
                ConditionTerm::machine_compare(*format, CompareRelation::Equal, left, right),
                value,
            );
        }
        // An equality naming a C narrowing conversion whose operand this
        // context already places inside the destination range also files the
        // conversion's identity with its operand (`narrowed_cast_identity`),
        // so equality reasoning relates `x == conv(y)` to `x == y`. One
        // memoized decision per bound of each converted side; nothing else
        // in the context is visited.
        if value
            && let ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } = &condition
        {
            for side in [left.as_ref(), right.as_ref()] {
                if matches!(
                    side,
                    MachineTerm::Cast {
                        spelling: MachineCastSpelling::Generic,
                        ..
                    }
                ) && let Some(carrier) = self.narrowed_cast_carrier(side)
                {
                    let identity = ConditionTerm::equal(side.clone(), carrier);
                    if identity != condition {
                        self = self.assume_condition_uncharged(identity, true);
                    }
                }
            }
        }
        // A fact that reads a stored cell also files its form over the value
        // stored there (the read-over-write authority,
        // `eval::read_over_write_value`), as a narrowing above files its
        // carrier: one bounded rewrite of this fact, nothing else visited.
        if let Some(Proposition::ConditionIs(resolved, resolved_value)) =
            crate::kernel::eval::comparison_form(&Proposition::condition_is(
                condition.clone(),
                value,
            ))
            && resolved.native_compat() != &condition
        {
            self =
                self.assume_condition_uncharged(resolved.native_compat().clone(), resolved_value);
        }
        // The graph derives a same-block comparison's offset view. Do not
        // publish it as an independent premise: it holds only in contexts that
        // hold the original pointer comparison.
        // An unsigned upper bound below the sign bit, the `uint32` order
        // `x <u c` with `c <= 2^31`, holds exactly when the signed pair
        // `0 <= x` and `x < c` does, so the pair is filed beside it, with the
        // source's strictness: every reader of signed order facts on `x`
        // (interval, index range, and element-membership rules) then sees
        // the range the unsigned test established, through the same indexes
        // it reads for a signed test. Two facts per bound, both on the
        // bounded term itself.
        //
        // A sixty-four-bit `x <u c` with `c <= 2^31` files the same pair on
        // the low word `(uint32)x`, which is `x` itself, and the sign-bit
        // bound `x <=u INT_MAX` that checked range projection asks for by key.
        if let Some((term, bound, strict)) =
            condition_reasoning::unsigned_upper_bound_below_sign_bit(&condition, value)
        {
            self = self.assume_unsigned_word_range(term.clone(), bound, strict);
        } else if let Some((term, bound, strict)) =
            condition_reasoning::uint64_upper_bound_below_sign_bit(&condition, value)
        {
            let term = term.clone();
            let sign_bit_clear = ConditionTerm::uint64_less_equal(
                term.clone(),
                MachineTerm::uint64_constant(i32::MAX as u64),
            );
            if sign_bit_clear != condition {
                self = self.assume_condition_uncharged(sign_bit_clear, true);
            }
            self =
                self.assume_unsigned_word_range(MachineTerm::uint32_from_64(term), bound, strict);
        }
        // Ordinary exact observations retain their written source and shared
        // comparison indexes. The operation bridge still handles an in-range
        // machine `+` or `-`: an Integer
        // comparison whose side is the exact value of such an operation,
        // `to_integer(a) <= 4294967295 - to_integer(b)` on `uint32`, holds
        // exactly when the native comparison of the operation does
        // (`a <= 4294967295u32 - b`), once the operation's result lies in
        // its type. A range bound the operands' types do not already imply
        // must be a fact here (`IntegerOperationRangeBound`). At most two
        // sides and two bounds of three spellings each are looked up.
        if let Some((view, bounds)) =
            (super::machine_integer::comparison::native_comparison_view(&condition, value)
                .is_none()
                && !super::machine_integer::modular::has_word_equality_projection(
                    &condition, value,
                ))
            .then(|| {
                super::machine_integer::comparison::comparison_view_through_integer_operations(
                    &condition, value,
                )
            })
            .flatten()
            && bounds
                .iter()
                .all(|bound| self.knows_operation_range_bound(bound))
        {
            self = self.assume_condition_uncharged(view.integer_condition(), true);
        }
        // Arithmetic domains stay as ordinary bounds. Overflow queries read
        // those bounds directly; do not publish a second opaque fact here.
        // Filing derived facts above can itself establish this condition.
        // Apply the same monotone rule before committing the original entry.
        if self.restates_condition(&condition, value) {
            return self;
        }
        self.execution_variable_ceiling.file_condition(&condition);
        self.condition_facts = self.condition_facts.with_inserted(condition.clone(), value);
        self.execution_fact_projection.insert(
            ContextFactKey::Condition(condition.clone()),
            std::sync::Arc::new(ExecutionPureFact::from_shared(source.unwrap_or_else(
                || std::sync::Arc::new(Proposition::condition_is(condition.clone(), value)),
            ))),
        );
        self.adjust_pointer_class_fact(&Proposition::condition_is(condition.clone(), value));
        self.adjust_memory_load_condition_index(&condition);
        self.adjust_stated_proposition_index(&Proposition::condition_is(condition.clone(), value));
        self.adjust_signed_order_bound(&condition, value);
        self.adjust_null_pointer_offset(&condition, value);
        self.adjust_address_base_alias(&condition, value);
        self.adjust_pointer_offset_alias(&condition, value);
        self.adjust_int32_graph_equality(&condition, value);
        self.adjust_uint64_graph_equality(&condition, value);
        self.adjust_algebraic_graph_equality(&Proposition::condition_is(condition.clone(), value));
        if value
            && matches!(
                condition,
                ConditionTerm::AddressEqual(..) | ConditionTerm::PointerEqual(..)
            )
        {
            self.composition_object_resources
                .advance_memory_equalities(&self);
        }
        self.adjust_scalar_evidence_input(&condition, value);
        self.adjust_bitvector64_equality(&condition, value);
        self.adjust_exact_constant_equality(&condition, value);

        self.adjust_condition_match_indexes(&condition, value);
        if self.equality_graph.add_condition(&condition, value) {
            self.equality_graph
                .admitted
                .congruence_conditions
                .insert(condition.clone(), value);
        }
        // A `Bool` value's binders take the truths their own facts gave them
        // (rule L-Eq): those facts may predate the value's classes.
        if condition.is_bool_value_form() {
            self.admit_bool_binder_truths(&condition);
        }
        self.content_fingerprint ^= Self::fingerprint(1, &(condition.clone(), value));
        self.admit_exact_propagation(Proposition::condition_is(condition, value));
        self
    }

    /// Admit, for each binder directly under a `Bool` value's conditionals
    /// and equalities, its own filed truth into the e-graph, where an L-Eq
    /// merge can carry it. One indexed lookup per binder of the value.
    fn admit_bool_binder_truths(&mut self, condition: &ConditionTerm) {
        let mut pending = vec![condition];
        while let Some(condition) = pending.pop() {
            match condition {
                ConditionTerm::Variable(_) => {
                    if let Some(value) = self.condition_facts.get(condition).copied()
                        && self.equality_graph.add_condition(condition, value)
                    {
                        self.equality_graph
                            .admitted
                            .congruence_conditions
                            .insert(condition.clone(), value);
                    }
                }
                condition => pending.extend(condition.bool_children()),
            }
        }
    }

    /// Files the range of the typed signed reading established by an unsigned
    /// bound below the sign bit: `0 <= signed(term)`, and
    /// `signed(term) < bound + 1` (strict source) or `signed(term) <= bound`.
    fn assume_unsigned_word_range(mut self, term: MachineTerm, bound: u32, strict: bool) -> Self {
        let term = condition_reasoning::signed_uint32_term(term);
        self = self.assume_condition_uncharged(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), term.clone()),
            true,
        );
        // A bound of `INT_MAX` says nothing every signed word does not.
        if bound == i32::MAX as u32 {
            self
        } else if strict {
            self.assume_condition_uncharged(
                ConditionTerm::signed_less_than(term, MachineTerm::constant(bound + 1)),
                true,
            )
        } else {
            self.assume_condition_uncharged(
                ConditionTerm::signed_less_equal(term, MachineTerm::constant(bound)),
                true,
            )
        }
    }

    /// This context extended by `proposition`, charged one unit of
    /// deterministic work (see [`Self::assume_condition`]).
    /// At least the greatest execution-range variable any of these facts
    /// mentions; see `ExecutionVariableCeiling`.
    pub(in crate::kernel) fn execution_variable_ceiling(&self) -> Option<Variable> {
        self.execution_variable_ceiling.get()
    }

    /// Share the admitted syntax with the store and with execution publication.
    pub(crate) fn assume_shared_proposition(
        mut self,
        proposition: std::sync::Arc<Proposition>,
    ) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        if let Proposition::ConditionIs(condition, value) = proposition.as_ref() {
            return self.assume_condition_with_source(
                (condition.clone()).native_compat().clone(),
                *value,
                Some(proposition.clone()),
            );
        }
        if let Proposition::Not(body) = proposition.as_ref() {
            if let Proposition::ConditionIs(condition, value) = body.as_ref() {
                return self.assume_condition_uncharged(
                    (condition.clone()).native_compat().clone(),
                    !*value,
                );
            }
            self.insert_shared_proposition_fact(proposition);
            return self;
        }
        if matches!(proposition.as_ref(), Proposition::And(..)) {
            return self.assume_proposition_uncharged(
                crate::kernel::clone_proposition_iteratively(&proposition),
            );
        }
        let decided = decided_algebraic_if(&proposition);
        let reduced = self.reduce_by_decided_conditions(&proposition);
        let native = self.shared_antecedent_reading(&proposition);
        self.insert_shared_proposition_fact(proposition);
        if let Some(native) = native {
            self.insert_proposition_fact(native);
        }
        if let Some((condition, value, selected)) = decided {
            self = self.assume_decided_algebraic_if(condition, value, selected);
        }
        if let Some(reduced) = reduced {
            self = self.assume_proposition_uncharged(reduced);
        }
        self
    }

    /// Indexed retrieval of an already retained exact syntax object. This is
    /// interning, not a proof query; opposite condition occurrences stay distinct.
    pub(crate) fn shared_assumed_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<std::sync::Arc<Proposition>> {
        let key = match proposition {
            Proposition::ConditionIs(condition, _) => {
                ContextFactKey::Condition((condition.clone()).native_compat().clone())
            }
            _ => ContextFactKey::Proposition(proposition.clone()),
        };
        self.execution_fact_projection
            .get(&key)
            .filter(|fact| fact.proposition() == proposition)
            .map(|fact| fact.shared_proposition())
    }

    pub fn assume_proposition(self, proposition: Proposition) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        self.assume_proposition_uncharged(proposition)
    }

    /// [`Self::assume_proposition`] without its charge, for a context build
    /// that is a known violation of the complexity contract
    /// (`docs/internals/verification-efficiency.md`) and whose charge would
    /// fail a scaling regression until its representation changes. Every
    /// caller names the violation it carries.
    pub(crate) fn assume_proposition_uncharged(mut self, proposition: Proposition) -> Self {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self = self.assume_condition_uncharged(condition.native_compat().clone(), value);
            }
            Proposition::And(left, right) => {
                self = self.assume_proposition_uncharged(*left);
                self = self.assume_proposition_uncharged(*right);
            }
            Proposition::Not(body) => match *body {
                Proposition::ConditionIs(condition, value) => {
                    self =
                        self.assume_condition_uncharged(condition.native_compat().clone(), !value);
                }
                body => {
                    self.insert_proposition_fact(Proposition::Not(Box::new(body)));
                }
            },
            proposition => {
                let decided = decided_algebraic_if(&proposition);
                let reduced = self.reduce_by_decided_conditions(&proposition);
                let native = self.shared_antecedent_reading(&proposition);
                self.insert_proposition_fact(proposition);
                if let Some(native) = native {
                    self.insert_proposition_fact(native);
                }
                if let Some((condition, value, selected)) = decided {
                    self = self.assume_decided_algebraic_if(condition, value, selected);
                }
                if let Some(reduced) = reduced {
                    self = self.assume_proposition_uncharged(reduced);
                }
            }
        }
        self
    }

    /// A quantified fact `forall k { A(k) implies B(k) }` whose antecedent
    /// compares the Integer value of an in-range machine `+` or `-`, such as
    /// `to_integer(k) < to_integer(len) + 1`, filed again with that
    /// comparison read through a shared machine operation. The two
    /// antecedents agree once each operation's result lies in its type, so a
    /// range bound the operand types do not imply must already be a fact, and
    /// it may not name the bound variable. Built-in checks that match a
    /// definition's quantified body fact exactly, such as assembling
    /// `cstr_at(p, len)`, then see what a specification stated with Integer
    /// arithmetic. The work is the antecedent's conjuncts, each one shape
    /// match and at most a few exact lookups.
    fn shared_antecedent_reading(&self, proposition: &Proposition) -> Option<Proposition> {
        let Proposition::ForAll {
            var,
            sort,
            body,
            name,
        } = proposition
        else {
            return None;
        };
        let Proposition::Implies(antecedent, consequent) = body.as_ref() else {
            return None;
        };
        let native = self.shared_conjunct_reading(antecedent, *var)?;
        Some(Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: Box::new(Proposition::Implies(Box::new(native), consequent.clone())),
            name: name.clone(),
        })
    }

    /// The native reading of each conjunct of `antecedent` that has one, or
    /// `None` when no conjunct changes.
    fn shared_conjunct_reading(
        &self,
        antecedent: &Proposition,
        var: Variable,
    ) -> Option<Proposition> {
        match antecedent {
            Proposition::And(left, right) => {
                let (native_left, native_right) = (
                    self.shared_conjunct_reading(left, var),
                    self.shared_conjunct_reading(right, var),
                );
                if native_left.is_none() && native_right.is_none() {
                    return None;
                }
                Some(Proposition::And(
                    Box::new(native_left.unwrap_or_else(|| left.as_ref().clone())),
                    Box::new(native_right.unwrap_or_else(|| right.as_ref().clone())),
                ))
            }
            Proposition::ConditionIs(condition, value) => {
                crate::instrumentation::record_deterministic_work(1);
                let (view, bounds) =
                    super::machine_integer::comparison::comparison_view_through_integer_operations(
                        condition.native_compat(),
                        *value,
                    )?;
                (bounds.iter().all(|bound| {
                        let facts = bound.stating_facts();
                        let mut variables = std::collections::BTreeSet::new();
                        for fact in &facts {
                            crate::kernel::reasoning::variable_collection::collect_proposition_capture_variables(
                                fact,
                                &mut variables,
                            );
                        }
                        !variables.contains(&var) && self.knows_operation_range_bound(bound)
                    }))
                .then(|| view.integer_proposition())
            }
            _ => None,
        }
    }

    /// What [`decided_algebraic_if`] found: the condition at its value and
    /// the remaining branch's equality, with that equality's field equalities
    /// when both sides apply one constructor, as constructor injectivity
    /// gives them.
    fn assume_decided_algebraic_if(
        mut self,
        condition: ConditionTerm,
        value: bool,
        selected: Proposition,
    ) -> Self {
        self.decided_algebraic_ifs = true;
        self = self.assume_condition_uncharged(condition, value);
        let fields = algebraic_constructor_field_equalities(&selected);
        self = self.assume_proposition_uncharged(selected);
        for field in fields.into_iter().flatten() {
            self = self.assume_proposition_uncharged(field);
        }
        self
    }

    /// `proposition` with each conditional whose condition an algebraic
    /// `if` equation decided here replaced by the branch it selects; `None`
    /// when no such equation was assumed or nothing changes. Only the
    /// proposition's own conditions are looked up.
    fn reduce_by_decided_conditions(&self, proposition: &Proposition) -> Option<Proposition> {
        if !self.decided_algebraic_ifs {
            return None;
        }
        let decided =
            crate::kernel::proof::term_rewrite::TermRewrite::conditional_guards(proposition)
                .into_iter()
                .filter_map(|condition| {
                    let value = self.selected_comparison_value(&condition)?;
                    Some((condition, value))
                })
                .collect::<std::collections::HashMap<_, _>>();
        if decided.is_empty() {
            return None;
        }
        let reduced = crate::kernel::proof::term_rewrite::TermRewrite::for_conditions(&decided)
            .proposition(proposition);
        (&reduced != proposition).then_some(reduced)
    }

    pub fn pure_facts(&self) -> Vec<Proposition> {
        let mut facts = self
            .condition_facts
            .scan_for_upkeep()
            .map(|(condition, value)| Proposition::condition_is(condition.clone(), *value))
            .collect::<Vec<_>>();
        facts.extend(self.prop_facts.scan_for_upkeep().cloned());
        facts
    }

    fn adjust_atomic_connection_fact(&mut self, proposition: &Proposition) {
        // These scalar dependencies already live in the shared syntax index;
        // this fragment has no state, block, or algebraic dependencies.
        if let Proposition::ConditionIs(condition, _) = proposition
            && self
                .shared_condition_variables
                .contains(condition.native_compat())
        {
            return;
        }
        let _timing =
            crate::instrumentation::OperationTiming::new("", "", "atomic dependency indexing");
        let all_keys =
            crate::kernel::reasoning::variable_collection::collect_atomic_connection_keys(
                proposition,
            );
        let mut keys = all_keys.clone();
        let mut covered_variables = 0;
        if let Proposition::ConditionIs(condition, _) = proposition {
            let has_variables = all_keys
                .iter()
                .any(|key| matches!(key, AtomicConnectionKey::Variable(_)));
            let mut indexed_variables = BTreeSet::new();
            let deferred = super::reasoning::variable_collection::collect_condition_index_variables(
                condition.native_compat(),
                &mut indexed_variables,
            );
            let covered = all_keys
                .iter()
                .filter_map(|key| match key {
                    AtomicConnectionKey::Variable(variable)
                        if !deferred && indexed_variables.contains(variable) =>
                    {
                        Some(*variable)
                    }
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            covered_variables = covered.len();
            keys.retain(|key| match key {
                AtomicConnectionKey::Variable(variable) => !covered.contains(variable),
                // SymbolicMemory state equations can define a load named by its address,
                // so retain their reverse address-block adjacency as well.
                // Scalar facts reuse their existing value-variable index.
                AtomicConnectionKey::Block(_) => !has_variables || covered.is_empty(),
            });
        }
        // Filing already charges the first entry. Existing scalar adjacency
        // covers its variables; charge only genuinely additional syntax keys.
        let extra_work = if covered_variables > 0 {
            keys.len()
        } else {
            keys.len().saturating_sub(1)
        };
        crate::instrumentation::record_deterministic_work(extra_work);
        let shared = SharedIndexFact::new(proposition.clone());
        if all_keys.is_empty() {
            self.atomic_ground_facts = self.atomic_ground_facts.with_value(shared.clone());
        }
        for key in keys {
            let mut bucket = self
                .atomic_connection_facts
                .get(&key)
                .cloned()
                .unwrap_or_default();
            let facts = if matches!(proposition, Proposition::ConditionIs(..)) {
                &mut bucket.conditions
            } else {
                &mut bucket.propositions
            };
            *facts = facts.with_value(shared.clone());
            if matches!(proposition, Proposition::Or(..)) {
                bucket.disjunctions = bucket.disjunctions.with_value(shared.clone());
            }
            self.atomic_connection_facts =
                if bucket.conditions.is_empty() && bucket.propositions.is_empty() {
                    self.atomic_connection_facts.without_key(&key)
                } else {
                    self.atomic_connection_facts.with_inserted(key, bucket)
                };
        }
        if matches!(proposition, Proposition::ForAll { .. }) {
            self.atomic_quantified_facts = self.atomic_quantified_facts.with_value(shared.clone());
            self.index_universal_equality(proposition);
            for key in UniversalConclusionKey::of(proposition) {
                crate::instrumentation::record_deterministic_work(1);
                let bucket = self
                    .universals_by_conclusion
                    .get(&key)
                    .cloned()
                    .unwrap_or_default();
                let bucket = bucket.with_value(shared.clone());
                self.universals_by_conclusion = if bucket.is_empty() {
                    self.universals_by_conclusion.without_key(&key)
                } else {
                    self.universals_by_conclusion.with_inserted(key, bucket)
                };
            }
        }
    }

    /// The universal facts whose conclusion takes the shape `key`, in
    /// `atomic_quantified_facts` order, so a `find` picks the fact a scan
    /// of every universal would.
    pub(in crate::kernel) fn universals_concluding(
        &self,
        key: UniversalConclusionKey,
    ) -> impl Iterator<Item = &Proposition> {
        crate::instrumentation::record_deterministic_work(1);
        self.universals_by_conclusion
            .get(&key)
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .map(|fact| {
                crate::instrumentation::record_deterministic_work(1);
                fact.as_ref()
            })
    }

    fn rebuild_atomic_connection_facts(&mut self) {
        self.atomic_connection_facts = crate::persistent::PersistentMap::default();
        self.atomic_ground_facts = crate::kernel::fact_collections::ScanSet::default();
        self.atomic_quantified_facts = crate::kernel::fact_collections::ScanSet::default();
        self.universals_by_conclusion = crate::persistent::PersistentMap::default();
        self.universal_equality_sources = Default::default();
        let conditions = self.condition_facts.clone();
        for (condition, value) in conditions.scan_for_upkeep() {
            self.adjust_atomic_connection_fact(&Proposition::condition_is(
                condition.clone(),
                *value,
            ));
        }
        let propositions = self.prop_facts.clone();
        for proposition in propositions.scan_for_upkeep() {
            self.adjust_atomic_connection_fact(proposition);
        }
    }

    fn condition_variable_facts(
        &self,
        variable: Variable,
    ) -> impl Iterator<Item = (&ConditionTerm, bool)> {
        let mut shared = self
            .shared_condition_variables
            .facts(variable)
            .into_iter()
            .peekable();
        let mut native = self
            .condition_facts_by_variable
            .get(&variable)
            .into_iter()
            .flat_map(|facts| facts.iter())
            .map(|(fact, value)| (fact.as_ref(), *value))
            .peekable();
        // Preserve source order without materializing the ordinary native bucket.
        std::iter::from_fn(
            move || match (native.peek().copied(), shared.peek().copied()) {
                (Some((a, _)), Some((b, _))) if a <= b => {
                    if a == b {
                        shared.next();
                    }
                    native.next()
                }
                (Some(_), Some(_)) | (None, Some(_)) => shared.next(),
                (Some(_), None) => native.next(),
                (None, None) => None,
            },
        )
    }

    pub(in crate::kernel) fn has_condition_variable(&self, variable: Variable) -> bool {
        self.condition_facts_by_variable
            .get(&variable)
            .is_some_and(|facts| !facts.is_empty())
            || self
                .shared_condition_variables
                .witnesses(variable)
                .next()
                .is_some()
    }

    fn singleton_condition_variable(&self, variable: Variable) -> Option<(&ConditionTerm, bool)> {
        let mut witnesses = self
            .condition_facts_by_variable
            .get(&variable)
            .into_iter()
            .flat_map(|facts| facts.iter().take(2))
            .map(|(fact, value)| (fact.as_ref(), *value))
            .chain(self.shared_condition_variables.witnesses(variable));
        let first = witnesses.next()?;
        witnesses.all(|next| next == first).then_some(first)
    }

    pub(crate) fn atomic_facts_connected_to(
        &self,
        key: &AtomicConnectionKey,
        include_propositions: bool,
    ) -> (impl Iterator<Item = AtomicConnectedFact<'_>>, bool) {
        let variable = match key {
            AtomicConnectionKey::Variable(variable) => Some(*variable),
            AtomicConnectionKey::Block(_) => None,
        };
        let scalar = variable
            .into_iter()
            .flat_map(|variable| self.condition_variable_facts(variable))
            .map(|(condition, value)| AtomicConnectedFact::Condition(condition, value));
        let bucket = self.atomic_connection_facts.get(key);
        let has_propositions = bucket.is_some_and(|bucket| !bucket.propositions.is_empty());
        let conditions = bucket.map(|bucket| &bucket.conditions);
        let propositions = include_propositions
            .then(|| bucket.map(|bucket| &bucket.propositions))
            .flatten();
        (
            scalar.chain(
                conditions
                    .into_iter()
                    .chain(propositions)
                    .flat_map(crate::persistent::PersistentSet::iter)
                    .map(|fact| AtomicConnectedFact::Proposition(fact.as_ref())),
            ),
            has_propositions,
        )
    }

    /// Only stated disjunctions in this operand's existing dependency bucket.
    /// Logical projection does not visit unrelated scalar or predicate facts.
    pub(crate) fn disjunctions_connected_to(
        &self,
        key: &AtomicConnectionKey,
    ) -> impl Iterator<Item = &Proposition> {
        self.atomic_connection_facts
            .get(key)
            .into_iter()
            .flat_map(|bucket| bucket.disjunctions.iter())
            .map(SharedIndexFact::as_ref)
    }

    /// Constant-time cardinalities for a selection drawn from these fact sets.
    pub(crate) fn fact_counts(&self) -> (usize, usize) {
        (self.condition_facts.len(), self.prop_facts.len())
    }

    /// The atomic ground and universal facts, for the planner's premise
    /// search.
    pub(crate) fn atomic_general_facts(
        &self,
        permission: crate::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.atomic_ground_facts
            .scan_for_search(&permission)
            .chain(self.atomic_quantified_facts.scan_for_search(&permission))
            .map(SharedIndexFact::as_ref)
    }

    /// The condition facts of this context, in the index's own order.
    ///
    /// This is a read-only view for a planner outside the kernel: it names
    /// what is available without exposing the index that stores it.
    #[cfg(test)]
    pub(crate) fn condition_fact_pairs(
        &self,
        permission: crate::SearchPermission,
    ) -> impl Iterator<Item = (&ConditionTerm, bool)> {
        self.condition_facts
            .scan_for_search(&permission)
            .map(|(condition, value)| (condition, *value))
    }

    /// Read-only variable adjacency for smart premise planning. MemoryState
    /// facts are indexed once on demand; this is necessary because a fact
    /// can connect to the goal through a variable stored in its state,
    /// even when their written syntax shares no variable. The kernel still
    /// checks every retained premise and the resulting atomic evidence.
    pub fn condition_facts_mentioning_variable(
        &self,
        variable: Variable,
    ) -> Option<impl Iterator<Item = (&ConditionTerm, bool)>> {
        let state_index = if let Some(index) = self.state_condition_variables.get() {
            index
        } else {
            let _timing = crate::instrumentation::OperationTiming::new(
                "",
                "",
                "state condition premise indexing",
            );
            let mut index = self.state_condition_variable_base.clone();
            for (condition, value) in self.state_condition_variable_changes.iter() {
                if reasoning_interrupted() {
                    return None;
                }
                let mut variables = BTreeSet::new();
                collect_condition_bitvector_variables(condition, &mut variables);
                let indexed = SharedIndexFact::new(condition.clone());
                for variable in variables {
                    crate::instrumentation::record_deterministic_work(1);
                    let facts = index.get(&variable).cloned().unwrap_or_default();
                    index =
                        index.with_inserted(variable, facts.with_inserted(indexed.clone(), *value));
                }
            }
            if reasoning_interrupted() {
                return None;
            }
            let _ = self.state_condition_variables.set(index);
            self.state_condition_variables.get()?
        };
        Some(
            self.condition_variable_facts(variable).chain(
                state_index
                    .get(&variable)
                    .into_iter()
                    .flat_map(|facts| facts.iter())
                    .map(|(condition, value)| (condition.as_ref(), *value)),
            ),
        )
    }

    /// The proposition facts of this context, in the index's own order.
    pub(crate) fn proposition_facts(
        &self,
        permission: crate::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.prop_facts.scan_for_search(&permission)
    }

    /// A bounded sample and the total cardinality, in condition-then-proposition
    /// index order. At most 32 facts are visited or cloned, regardless of the
    /// requested sizes. Entries shared by the prefix and suffix appear once.
    pub(crate) fn diagnostic_fact_sample(
        &self,
        first: usize,
        last: usize,
    ) -> (Vec<Proposition>, usize) {
        let first = first.min(crate::kernel::fact_collections::DIAGNOSTIC_FACT_LIMIT);
        let last = last.min(crate::kernel::fact_collections::DIAGNOSTIC_FACT_LIMIT - first);
        let (conditions, propositions) = self.fact_counts();
        let first_conditions = first.min(conditions);
        let first_propositions = (first - first_conditions).min(propositions);
        let last_propositions = last.min(propositions - first_propositions);
        let last_conditions = (last - last_propositions).min(conditions - first_conditions);
        let facts = self
            .condition_facts
            .diagnostic_sample(first_conditions, last_conditions)
            .into_iter()
            .map(|(condition, value)| Proposition::condition_is(condition.clone(), *value))
            .chain(
                self.prop_facts
                    .diagnostic_sample(first_propositions, last_propositions)
                    .into_iter()
                    .cloned(),
            )
            .collect();
        (facts, conditions + propositions)
    }

    /// Answers whether a requirement is already stated in this context.
    /// Accepts explicit facts, conjunctions of them, and implications whose
    /// consequent is already stated. This query never selects a disjunction arm, instantiates a
    /// universal, or invents an existential witness.
    pub(crate) fn states_required_goal(&self, goal: &Proposition) -> bool {
        if let Proposition::And(left, right) = goal {
            return self.states_required_goal(left) && self.states_required_goal(right);
        }
        if let Proposition::Implies(_, consequent) = goal
            && self.states_required_goal(consequent)
        {
            // A proved conclusion also proves any guarded version of it.
            // This is needed when lowering has already discharged a generated
            // arithmetic guard in the surface spelling of a call requirement.
            return true;
        }
        // Loads emitted from a callee contract may retain its entry state
        // while the caller's retained fact uses the registered load variable.
        // Canonicalize a condition leaf through the kernel's load naming law
        // before consulting the exact stated-fact index; this is not logical
        // search and does not apply to memory-loadable/resource predicates.
        let canonical = crate::kernel::canonical_condition_fact(goal);
        if canonical != *goal {
            return self.states_required_goal(&canonical);
        }
        if let Some(key) = crate::kernel::proof::proposition_identity_key(goal)
            && let Some(bucket) = self
                .stated_proposition_index()
                .and_then(|index| index.get(&key))
            && let Some(candidate) = bucket.iter().next()
        {
            // The key narrows the lookup to one identity bucket; retain the
            // relation as the final authority so future key representations
            // cannot silently broaden this query.
            return crate::kernel::proof::propositions_are_alpha_equal(candidate, goal);
        }
        // Unsupported proposition forms retain the old exact route.  This is
        // still a named fact check and never scans for a related proposition.
        self.contains_assumed_exact(goal)
    }

    /// One checked restriction: a context carrying exactly the named
    /// condition facts and proposition facts, with every derived index
    /// rebuilt from them.
    ///
    /// This is the only operation by which a planner outside the kernel
    /// narrows a context to a premise selection, so no caller reaches the
    /// private fact indexes or their rebuild hooks. The non-fact settings of
    /// `self` (transport and deferral flags) are preserved, because a
    /// restricted context must answer under the same regime as the context
    /// it was cut from.
    pub fn restricted_to_facts(
        &self,
        conditions: &[(ConditionTerm, bool)],
        propositions: &[Proposition],
    ) -> Self {
        let _checking = crate::instrumentation::CheckingWorkScope::new(
            "restrict to selected facts",
            conditions.len().saturating_add(propositions.len()),
        );
        // Start from selected input, never withdraw inherited pointer sources.
        // Only retained typing metadata is consulted by selected load-variable key.
        let mut restricted = Self::new();
        restricted.reasoning_policy = self.reasoning_policy;
        restricted.execution_variable_ceiling = self.execution_variable_ceiling.clone();
        restricted.variable_widths = self.variable_widths.clone();
        restricted
            .equality_graph
            .admitted
            .typed_pointer_read_definitions = self
            .equality_graph
            .admitted
            .typed_pointer_read_definitions
            .clone();
        for (condition, _) in conditions {
            restricted
                .execution_variable_ceiling
                .file_condition(condition);
        }
        restricted.condition_facts = conditions.iter().fold(
            crate::kernel::fact_collections::FactMap::default(),
            |facts, (condition, value)| facts.with_inserted(condition.clone(), *value),
        );
        restricted.execution_fact_projection = conditions
            .iter()
            .map(|(condition, value)| {
                (
                    ContextFactKey::Condition(condition.clone()),
                    std::sync::Arc::new(ExecutionPureFact::new(Proposition::condition_is(
                        condition.clone(),
                        *value,
                    ))),
                )
            })
            .collect();
        // Condition support is replaced next. Reconstructing the inherited
        // graph here would reconstruct unselected ambient edges, then discard it.
        restricted.clear_proposition_facts();
        restricted.rebuild_signed_order_bounds();
        restricted.rebuild_null_pointer_offsets();
        restricted.rebuild_memory_load_condition_facts();
        restricted.rebuild_condition_match_indexes();
        for (condition, value) in conditions {
            restricted
                .admit_exact_propagation(Proposition::condition_is(condition.clone(), *value));
        }
        // File proposition edges and resource indexes only after their
        // condition graph is the selected one, never the inherited graph.
        for proposition in propositions {
            restricted.insert_proposition_fact(proposition.clone());
        }
        restricted.recompute_content_fingerprint();
        restricted
    }

    /// Ambient loadability facts for planner witness selection, charged per visit.
    /// Diagnostics use the block-keyed candidate view instead.
    pub(crate) fn memory_loadable_fact_propositions(
        &self,
        _permission: crate::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.memory_loadable_facts
            .values()
            .flat_map(|facts| facts.iter())
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The disjunction facts of this context, in the index's own order, for
    /// a planner's case search.
    pub(crate) fn disjunction_fact_propositions(
        &self,
        permission: crate::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.disjunction_facts.scan_for_search(&permission)
    }

    /// Whether this context holds a disjunction fact.
    pub fn has_disjunction_facts(&self) -> bool {
        !self.disjunction_facts.is_empty()
    }

    /// Whether `proposition` is an exact proposition fact of this context.
    pub fn contains_proposition_fact(&self, proposition: &Proposition) -> bool {
        self.prop_facts.contains(proposition)
            || (!self.comparison_views.is_empty()
                && self
                    .comparison_views
                    .get(&observation_comparisons::PropositionKey::new(proposition))
                    .is_some())
            || matches!(&proposition, condition_source_0 @ Proposition::ConditionIs(_, truth) if matches!(condition_source_0.condition_native(), Some((condition @ ConditionTerm::Compare { .. }, _)) if (self.observation_comparisons.source(condition, *truth).is_some())))
    }

    pub(super) fn includes(&self, required: &Self) -> bool {
        required
            .condition_facts
            .scan_explicit_input()
            .all(|(condition, value)| {
                self.contains_assumed_exact(&Proposition::condition_is(condition.clone(), *value))
            })
            && required
                .equality_graph
                .admitted
                .typed_pointer_read_definitions
                .iter()
                .all(|(variable, definitions)| {
                    self.equality_graph
                        .admitted
                        .typed_pointer_read_definitions
                        .get(variable)
                        .is_some_and(|held| {
                            definitions
                                .iter()
                                .all(|(key, value)| held.get(key) == Some(value))
                        })
                })
            && required
                .prop_facts
                .scan_explicit_input()
                .all(|proposition| self.contains_assumed_exact(proposition))
            && required
                .resource_compositions
                .scan_explicit_input()
                .all(|resources| self.resource_compositions.contains(resources))
    }
}

pub(crate) fn proposition_derivation(
    conclusion: &Proposition,
    rule: PropositionDerivationRule,
) -> PropositionDerivation {
    PropositionDerivation {
        conclusion: conclusion.clone(),
        rule,
    }
}

impl PropositionDerivation {
    /// Check this proof tree against an available context without searching for
    /// alternate proofs.
    #[inline(never)]
    pub fn check(&self, available: &PureFactContext) -> bool {
        let id_scope = PureFactContextIdScope::enter(available);
        match &self.rule {
            PropositionDerivationRule::ContextFree => solve_builtin_prop(&self.conclusion),
            PropositionDerivationRule::ContextualAtomic {
                premises,
                premises_id,
                extended_rules,
                evidence,
            } => {
                let premises = premises.context();
                (id_scope.id == *premises_id || available.includes(&premises))
                    && premises.checks_atomic_derivation(
                        &self.conclusion,
                        *extended_rules,
                        *premises_id,
                        evidence,
                    )
            }
            PropositionDerivationRule::Explosion { premises } => {
                let premises = premises.context();
                available.includes(&premises) && premises.is_inconsistent()
            }
            PropositionDerivationRule::And { left, right } => {
                let Proposition::And(expected_left, expected_right) = &self.conclusion else {
                    return false;
                };
                left.conclusion == **expected_left
                    && right.conclusion == **expected_right
                    && left.check(available)
                    && right.check(available)
            }
            PropositionDerivationRule::AlgebraicConstructorCongruence { fields } => {
                let Some(expected) = algebraic_constructor_field_equalities(&self.conclusion)
                else {
                    return false;
                };
                !expected.is_empty()
                    && derivations_match_propositions(fields, &expected)
                    && fields.iter().all(|proof| proof.check(available))
            }
            PropositionDerivationRule::AlgebraicConstructorInjectivity {
                source,
                field_index,
            } => {
                let Some(expected) = algebraic_constructor_field_equalities(source)
                    .and_then(|fields| fields.get(*field_index).cloned())
                else {
                    return false;
                };
                expected == self.conclusion && available.prop_facts.contains(source.as_ref())
            }
            PropositionDerivationRule::OrLeft(proof) => {
                let Proposition::Or(expected, _) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **expected && proof.check(available)
            }
            PropositionDerivationRule::OrRight(proof) => {
                let Proposition::Or(_, expected) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **expected && proof.check(available)
            }
            PropositionDerivationRule::DoubleNegation(proof) => {
                let Proposition::Not(body) = &self.conclusion else {
                    return false;
                };
                let Proposition::Not(expected) = body.as_ref() else {
                    return false;
                };
                proof.conclusion == **expected && proof.check(available)
            }
            PropositionDerivationRule::Implies { antecedent, body } => {
                let Proposition::Implies(expected_antecedent, expected_body) = &self.conclusion
                else {
                    return false;
                };
                antecedent.as_ref() == expected_antecedent.as_ref()
                    && body.conclusion == **expected_body
                    && body.check(
                        &available
                            .clone()
                            .assume_proposition(antecedent.as_ref().clone()),
                    )
            }
            PropositionDerivationRule::ImpliesFalseAntecedent(proof) => {
                let Proposition::Implies(expected_antecedent, _) = &self.conclusion else {
                    return false;
                };
                proof.conclusion == Proposition::Not(Box::new(expected_antecedent.as_ref().clone()))
                    && proof.check(available)
            }
            PropositionDerivationRule::ForAllBody(proof) => {
                let Proposition::ForAll { var, body, .. } = &self.conclusion else {
                    return false;
                };
                proof.conclusion == **body
                    && (!proposition_has_free_bitvector_variable(body, *var)
                        || proof
                            .context_premises()
                            .iter()
                            .all(|premise| !proposition_has_free_bitvector_variable(premise, *var)))
                    && proof.check(available)
            }
            PropositionDerivationRule::ExistsFromFact { source, body } => {
                let Proposition::Exists {
                    var,
                    sort,
                    body: expected_body,
                    ..
                } = &self.conclusion
                else {
                    return false;
                };
                let Proposition::Exists {
                    var: source_var,
                    sort: source_sort,
                    body: source_body,
                    ..
                } = source.as_ref()
                else {
                    return false;
                };
                if sort != source_sort
                    || !available.proves_exact(source)
                    || body.conclusion != **expected_body
                {
                    return false;
                }
                let Some(renamed_source_body) =
                    crate::kernel::api::substitute_quantified_body_capture_free(
                        source_body,
                        *source_var,
                        *var,
                        sort,
                    )
                else {
                    return false;
                };
                let mut witness_available = available.clone();
                let mut conjuncts = Vec::new();
                collect_proposition_conjuncts(&renamed_source_body, &mut conjuncts);
                for conjunct in conjuncts {
                    witness_available = witness_available.assume_proposition(conjunct);
                }
                body.check(&witness_available)
            }
            PropositionDerivationRule::ExistsFromWitness { witness, body } => {
                let Proposition::Exists {
                    var,
                    body: expected_body,
                    ..
                } = &self.conclusion
                else {
                    return false;
                };
                let mut witness_variables = BTreeSet::new();
                collect_bitvector_variables(witness, &mut witness_variables);
                if witness_variables.contains(var) {
                    return false;
                }
                let instantiated =
                    substitute_bitvector_variable_in_proposition(expected_body, *var, witness);
                body.conclusion == instantiated && body.check(available)
            }
            PropositionDerivationRule::ForAllLoadableRange { source } => {
                available.proves_exact(source)
                    && available.checks_forall_loadable_range(&self.conclusion, source)
            }
            PropositionDerivationRule::FiniteForAll { instances } => {
                let mut expected = available.finite_forall_instantiations(&self.conclusion);
                !instances.is_empty()
                    && instances.iter().all(|proof| {
                        expected
                            .next()
                            .is_some_and(|conclusion| proof.conclusion == conclusion)
                            && proof.check(available)
                    })
                    && expected.next().is_none()
            }
            PropositionDerivationRule::SingletonSubstitution {
                variable,
                value,
                equality,
                body,
            } => {
                let variable_term = MachineTerm::Variable(*variable);
                let constant = signed_i64_bitvector_constant(*value);
                let Ok(expected) =
                    crate::kernel::reasoning::substitute_machine_constant_in_pure_proposition(
                        &self.conclusion,
                        *variable,
                        *value,
                    )
                else {
                    return false;
                };
                expected != self.conclusion
                    && body.conclusion == expected
                    && equality.checks(&variable_term, &constant, available)
                    && body.check(available)
            }
            PropositionDerivationRule::RefutedDisjunction { disjunction } => {
                let mut cases = Vec::new();
                collect_or_cases(disjunction, &mut cases);
                cases.len() >= 2
                    && available.contains_assumed_exact(disjunction)
                    && cases.iter().all(|case| {
                        available.contains_assumed_exact(&Proposition::Not(Box::new(case.clone())))
                    })
            }
            PropositionDerivationRule::DisjunctionCases { disjunction, cases } => {
                if !available.prop_facts.contains(disjunction.as_ref()) {
                    return false;
                }
                let mut expected_cases = Vec::new();
                collect_or_cases(disjunction, &mut expected_cases);
                if expected_cases.len() < 2 || cases.len() != expected_cases.len() {
                    return false;
                }
                cases.iter().zip(expected_cases).all(|(proof, case)| {
                    proof.conclusion == self.conclusion
                        && proof.check(&available.clone().assume_proposition(case))
                })
            }
        }
    }
}

/// Whether `term`'s arithmetic names a pointer address, the shape the
/// integer-to-pointer cast recovers a pointer from.
fn mentions_pointer_address(term: &MachineTerm) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if matches!(term, MachineTerm::IntegerAddress(..)) {
            return true;
        }
        if let Some((_, left, right)) = term.as_binary() {
            pending.push(left);
            pending.push(right);
        } else if let Some((_, value)) = term.as_unary() {
            pending.push(value);
        }
    }
    false
}

pub(crate) fn collect_proposition_conjuncts(
    proposition: &Proposition,
    into: &mut Vec<Proposition>,
) {
    match proposition {
        Proposition::And(left, right) => {
            collect_proposition_conjuncts(left, into);
            collect_proposition_conjuncts(right, into);
        }
        other => into.push(other.clone()),
    }
}

fn derivations_match_propositions(
    derivations: &[PropositionDerivation],
    propositions: &[Proposition],
) -> bool {
    derivations.len() == propositions.len()
        && derivations
            .iter()
            .zip(propositions)
            .all(|(derivation, proposition)| derivation.conclusion == *proposition)
}

fn relative_range_offset(value: &MachineTerm, origin: &MachineTerm) -> MachineTerm {
    match (value, origin) {
        (
            binary_term!(Int32, Subtract, value, value_origin),
            binary_term!(Int32, Subtract, origin, origin_origin),
        ) if value_origin == origin_origin => {
            MachineTerm::subtract(value.as_ref().clone(), origin.as_ref().clone())
        }
        _ => MachineTerm::subtract(value.clone(), origin.clone()),
    }
}

fn signed_int_min_term() -> MachineTerm {
    MachineTerm::constant(i32::MIN as u32)
}

fn signed_int_max_term() -> MachineTerm {
    MachineTerm::constant(i32::MAX as u32)
}

fn range_intervals_cover_target(target: &MemoryRange, mut intervals: Vec<(i64, i64)>) -> bool {
    let Some(target_start) = target.signed_constant_start() else {
        return false;
    };
    let Some(target_end) = target.signed_constant_end() else {
        return false;
    };
    if target_end <= target_start {
        return true;
    }

    intervals.sort_unstable();
    let mut covered_until = target_start;
    for (start, end) in intervals {
        let start = start.max(target_start);
        let end = end.min(target_end);
        if end <= covered_until {
            continue;
        }
        if start > covered_until {
            return false;
        }
        covered_until = end;
        if covered_until >= target_end {
            return true;
        }
    }
    false
}

// Called only by memory_ranges_proven_equal after its wide-range branch.
fn memory_range_length_term(range: &MemoryRange) -> MachineTerm {
    match range.end() {
        binary_term!(Int32, Add, base, length) if base.as_ref() == range.start() => {
            length.as_ref().clone()
        }
        binary_term!(Int32, Add, length, base) if base.as_ref() == range.start() => {
            length.as_ref().clone()
        }
        end => MachineTerm::subtract(end.clone(), range.start().clone()),
    }
}

/// Whether every cell of `range` is a cell of `parent`, for a caller with no
/// fact context. See [`memory_range_shallowly_contained_with_facts`].
pub(in crate::kernel) fn memory_range_shallowly_contained(
    range: &MemoryRange,
    parent: &MemoryRange,
) -> bool {
    memory_range_contained_by_exact_arithmetic(range, parent, None)
}

/// [`memory_range_shallowly_contained`] for a caller that holds a fact context.
///
/// This is `memory_range_covers`'s structural arm, so it gates every `owns` and
/// `views` entailment, contract-effect coverage and `free` span. It concluded
/// containment from two affine differences of modular terms read as signed
/// orders, and that is the same misreading `bitvector_index_outside_range_shallow`
/// carried, in the direction where it is unsound: a difference of `2^32` is not
/// "at or after", it is "the same element".
///
/// What containment means is an `i64` statement about addresses. `parent` holds
/// `parent_count` elements from the address of its element `parent.start`;
/// `range` holds `range_count` from the address of its own element
/// `range.start`, which sits `offset` elements into the parent. So containment
/// is `0 <= offset` and `offset + range_count <= parent_count`, and each of the
/// three is computed exactly or not at all:
///
/// * `offset` is the base delta plus `sext(range.start) - sext(parent.start)`.
///   The delta comes from [`Address::exact_element_delta_from_base`] as an
///   exact `i64` constant beside at most one symbolic index; the subtraction
///   comes from [`exact_affine_index_difference_views`]. Because only one symbolic
///   index may appear, whichever of the two ranges is rebased must carry a
///   constant start — which is what the shapes that reach here do: a child at
///   the parent's own base, or a child `[0..k]` at a pointer into the parent.
/// * both counts come from [`affine_range_element_count`], which is the count
///   and not a bound on it.
///
/// Ranges with different element widths have a narrower route: all endpoints
/// and the byte delta between their bases must be constant. Checked `i64`
/// multiplication and addition then compare their exact byte intervals. This
/// connects raw construction storage with typed field footprints without
/// treating symbolic or modular endpoint arithmetic as byte arithmetic.
///
/// A parent whose endpoints have no constant difference has no count, and then
/// the only route left compares the two ranges' *ends* — `p[3..n]` inside
/// `p[0..n]`. That reads `end` as `start + count`, so it additionally asks
/// [`range_count_is_nonnegative`] of the parent, which a stated span guard
/// supplies and a context-free caller cannot.
pub(in crate::kernel) fn memory_range_shallowly_contained_with_facts(
    range: &MemoryRange,
    parent: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    memory_range_contained_by_exact_arithmetic(range, parent, Some(assumptions))
}

fn memory_range_contained_by_exact_arithmetic(
    range: &MemoryRange,
    parent: &MemoryRange,
    assumptions: Option<&PureFactContext>,
) -> bool {
    if range.wide_bounds().is_some() || parent.wide_bounds().is_some() {
        return assumptions.is_some_and(|assumptions| {
            crate::kernel::primitives::wide_memory_range_covers(parent, range, assumptions)
        });
    }
    if range.element_width() != parent.element_width() {
        // Construction owns raw bytes while a constructor's write footprint
        // names typed fields. Constant bounds can be compared in exact byte
        // coordinates without modular arithmetic or changing either range.
        let Some(delta) = range
            .base()
            .exact_element_delta_from_base(parent.base(), 1, assumptions)
        else {
            return false;
        };
        if !delta.is_constant() {
            return false;
        }
        let byte_endpoint = |endpoint: &MachineTerm, width: u32, offset: i64| {
            signed_bitvector_constant(endpoint)?
                .checked_mul(i64::from(width))?
                .checked_add(offset)
        };
        let (Some(start), Some(end), Some(parent_start), Some(parent_end)) = (
            byte_endpoint(range.start(), range.element_width(), delta.constant),
            byte_endpoint(range.end(), range.element_width(), delta.constant),
            byte_endpoint(parent.start(), parent.element_width(), 0),
            byte_endpoint(parent.end(), parent.element_width(), 0),
        ) else {
            return false;
        };
        return parent_start <= start && start <= end && end <= parent_end;
    }
    let Some(base_delta) = range.base().exact_element_delta_from_base(
        parent.base(),
        parent.element_width(),
        assumptions,
    ) else {
        return false;
    };
    // `range`'s endpoints are in its own base's coordinates and `parent`'s are
    // in the parent's, so the base delta joins them. Only one symbolic index
    // may cross that join, since adding two would need the modular add this
    // whole rule exists to stop trusting.
    let translate = |endpoint: &MachineTerm| {
        if base_delta.is_constant() {
            Some((
                MachineOperandView::Legacy(endpoint).retain(MachineIntegerType::Int32),
                base_delta.constant,
            ))
        } else {
            signed_bitvector_constant(endpoint)
                .and_then(|endpoint| base_delta.constant.checked_add(endpoint))
                .map(|constant| (base_delta.index.clone(), constant))
        }
    };
    let Some((start_term, start_constant)) = translate(range.start()) else {
        return false;
    };
    let Some(offset) = exact_affine_index_difference_views(
        start_term.operand_view(),
        MachineOperandView::Legacy(parent.start()),
        assumptions,
    )
    .and_then(|difference| difference.checked_add(start_constant)) else {
        return false;
    };
    if offset < 0 {
        return false;
    }
    if let (Some(range_count), Some(parent_count)) = (
        affine_range_element_count(range.start(), range.end()),
        affine_range_element_count(parent.start(), parent.end()),
    ) && offset
        .checked_add(range_count)
        .is_some_and(|end| end <= parent_count)
    {
        return true;
    }
    let Some((end_term, end_constant)) = translate(range.end()) else {
        return false;
    };
    let Some(slack) = exact_affine_index_difference_views(
        MachineOperandView::Legacy(parent.end()),
        end_term.operand_view(),
        assumptions,
    )
    .and_then(|difference| difference.checked_sub(end_constant)) else {
        return false;
    };
    let Some(reach) = offset.checked_add(slack) else {
        return false;
    };
    slack >= 0
        && reach < (1i64 << 31)
        && (reach == 0 || range_count_is_nonnegative(parent, assumptions))
}

pub(super) fn memory_range_contained_for_memory_resolution(
    range: &MemoryRange,
    parent: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // Exact constant byte intervals cover typed accesses even when one side
    // uses raw bytes or int32 words. Symbolic cross-width containment remains
    // refused; the recursive element-index rules below require equal widths.
    if memory_range_shallowly_contained_with_facts(range, parent, assumptions) {
        return true;
    }
    if range.wide_bounds().is_some() || parent.wide_bounds().is_some() {
        return false;
    }
    if range.element_width() != parent.element_width() {
        return false;
    }
    if super::reasoning::resolution_interrupted() {
        return false;
    }
    let Some(_query) = super::reasoning::ResolutionQueryGuard::enter(
        super::reasoning::ResolutionQuery::RangeContained(range.clone(), parent.clone()),
    ) else {
        return false;
    };

    if super::reasoning::pointers_proven_equal_for_memory_resolution(
        range.base(),
        parent.base(),
        assumptions,
    ) {
        return exact_less_equal_for_memory_resolution(parent.start(), range.start(), assumptions)
            && exact_less_equal_for_memory_resolution(range.end(), parent.end(), assumptions);
    }

    if affine_bitvector_difference_constant(range.end(), range.start()) == Some(1) {
        let pointer = range.base().offset_by_int32_elements(range.start().clone());
        if pointer_in_memory_range_for_memory_resolution(&pointer, parent, assumptions) {
            return true;
        }
    }

    false
}

fn exact_less_equal_for_memory_resolution(
    left: &MachineTerm,
    right: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    if let (Some(left), Some(right)) = (
        signed_bitvector_constant(left),
        signed_bitvector_constant(right),
    ) {
        return left <= right;
    }
    if left == right
        // These are signed int32 endpoint *values*, not exact byte offsets.
        // Equal bitpatterns therefore satisfy `<=` in this same-base check.
        || assumptions.int32_values_known_equal(left, right)
        || assumptions.exact_condition_value(&ConditionTerm::signed_less_equal(
            left.clone(),
            right.clone(),
        )) == Some(true)
        || assumptions.has_exact_order_path(left, right, false)
    {
        return true;
    }
    let left_constant = signed_bitvector_constant(left);
    if recorded_less_equal_candidates(left, right, assumptions).any(
        |(fact_lower, _fact_upper, strict)| {
            // The written fact states `fact_lower <= fact_upper` (or `<`, which
            // is stronger). It proves the query when its lower endpoint is the
            // query's lower endpoint, or — for a constant query endpoint — when
            // it is a constant at least as large.
            if crate::kernel::reasoning::int32_operand_values_equal_for_memory_resolution(
                fact_lower,
                MachineOperandView::Legacy(left),
                assumptions,
            ) {
                return true;
            }
            let Some(left_constant) = left_constant else {
                return false;
            };
            fact_lower
                .word32_constant()
                .map(|bits| i64::from(bits as i32))
                .is_some_and(|bound| left_constant <= if strict { bound + 1 } else { bound })
        },
    ) {
        return true;
    }
    // Keep broader scalar-resolution rules for forms outside graph closure or
    // the indexed order facts, without building their fact index first.
    bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
}

#[cfg(test)]
mod contained_range_endpoint_graph_tests {
    use super::*;

    fn variable(id: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(id))
    }

    fn endpoint(id: u64) -> MachineTerm {
        MachineTerm::add(variable(id), MachineTerm::constant(1))
    }

    #[test]
    fn signed_containment_order_uses_graph_value_equality() {
        let premise = ConditionTerm::equal(variable(9_330_001), variable(9_330_002));
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(exact_less_equal_for_memory_resolution(
            &endpoint(9_330_001),
            &endpoint(9_330_002),
            &branch,
        ));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!exact_less_equal_for_memory_resolution(
            &endpoint(9_330_001),
            &endpoint(9_330_002),
            &parent,
        ));
    }

    #[test]
    fn same_base_range_containment_uses_graph_equal_endpoints() {
        let base = Address::symbolic(Variable(9_330_003));
        let parent = MemoryRange::new(base.clone(), MachineTerm::constant(0), endpoint(9_330_001));
        let child = MemoryRange::new(base.clone(), MachineTerm::constant(0), endpoint(9_330_002));
        let premise = ConditionTerm::equal(variable(9_330_001), variable(9_330_002));
        let bare = PureFactContext::new();
        let branch = bare.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();

        assert!(!memory_range_shallowly_contained_with_facts(
            &child, &parent, &branch,
        ));
        assert!(memory_range_contained_for_memory_resolution(
            &child, &parent, &branch,
        ));
        assert!(!memory_range_contained_for_memory_resolution(
            &child, &parent, &bare,
        ));
        let other_base = child.with_bounds(
            Address::symbolic(Variable(9_330_004)),
            child.start().clone(),
            child.end().clone(),
        );
        assert!(!memory_range_contained_for_memory_resolution(
            &other_base,
            &parent,
            &branch,
        ));
    }

    #[test]
    fn recorded_order_fact_matches_graph_equal_lower_or_upper_endpoint() {
        let lower = variable(9_330_010);
        let upper = variable(9_330_011);
        let premise = ConditionTerm::equal(variable(9_330_001), variable(9_330_002));
        let lower_fact = ConditionTerm::signed_less_equal(endpoint(9_330_001), upper.clone());
        let upper_fact = ConditionTerm::signed_less_than(lower.clone(), endpoint(9_330_001));
        let bare = PureFactContext::new()
            .assume_condition(lower_fact, true)
            .assume_condition(upper_fact, true);
        let branch = bare.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();

        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(exact_less_equal_for_memory_resolution(
            &endpoint(9_330_002),
            &upper,
            &branch,
        ));
        assert!(exact_less_equal_for_memory_resolution(
            &lower,
            &endpoint(9_330_002),
            &branch,
        ));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!exact_less_equal_for_memory_resolution(
            &endpoint(9_330_002),
            &upper,
            &bare,
        ));
        assert!(!exact_less_equal_for_memory_resolution(
            &lower,
            &endpoint(9_330_002),
            &bare,
        ));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/contained_range_endpoint_graph_tests.rs");
    }
}

/// The recorded `a <= b` and `a < b` facts whose upper endpoint is the named
/// `right`, or whose lower endpoint is the named `left`, as `(a, b)` pairs.
///
/// This replaces two scans of the whole ambient condition-fact set. Every
/// signed-order fact is already indexed at both of its endpoints — under the
/// term the fact wrote and under that term's canonical form — by
/// `PureFactContext::signed_order_bounds`, so the candidates a containment
/// query could use are reachable in work proportional to the bounds recorded
/// at the two endpoints the query itself names. Each candidate is then
/// confirmed against `condition_facts` by exact lookup, so the index's
/// normalization of `>`, `>=`, and negated forms cannot widen the rule: only
/// a written true `<=` or `<` is yielded, exactly as the scans required.
///
/// Narrowing, deliberate and measured: a fact whose relevant endpoint is
/// neither syntactically nor canonically the query's endpoint, and is only
/// *provably* equal to it, is no longer found. Reaching it needed a
/// proof-aware comparison against every ambient condition fact, which is the
/// scan this removes. `satisfies_fact_miss_ignores_unrelated_facts` is the
/// scaling regression.
fn recorded_less_equal_candidates<'a>(
    left: &'a MachineTerm,
    right: &'a MachineTerm,
    assumptions: &'a PureFactContext,
) -> impl Iterator<Item = (MachineOperandView<'a>, MachineOperandView<'a>, bool)> + 'a {
    let endpoint_keys = |term: &MachineTerm| {
        let canonical = crate::kernel::eval::canonical_term(term);
        if canonical == *term {
            vec![term.clone()]
        } else {
            vec![term.clone(), canonical]
        }
    };
    let endpoints = endpoint_keys(right)
        .into_iter()
        .map(|key| (key, false))
        .chain(endpoint_keys(left).into_iter().map(|key| (key, true)));
    endpoints
        .flat_map(move |(key, forward)| {
            assumptions
                .signed_order_bounds
                .get(&key)
                .into_iter()
                .flat_map(|bounds| bounds.written_signed_operands())
                .filter(move |(_, _, _, own_is_lower)| *own_is_lower == forward)
                .map(move |(own, other, strict, _)| {
                    if forward {
                        (own, other, strict)
                    } else {
                        (other, own, strict)
                    }
                })
        })
        .filter(move |(_, upper, _)| {
            crate::kernel::reasoning::int32_operand_values_equal_for_memory_resolution(
                *upper,
                MachineOperandView::Legacy(right),
                assumptions,
            )
        })
}

/// [`pointer_in_range_shallow`] over a range, for a caller with no fact
/// context: a structural or memoized walk that cannot consult one. It answers
/// only what arithmetic settles on its own — a pointer at the range's own start
/// term, or wholly constant endpoints and delta — and refuses the rest rather
/// than reading a residue as an offset.
pub(in crate::kernel) fn pointer_in_memory_range_shallow(
    pointer: &Address,
    range: &MemoryRange,
) -> bool {
    // A wide range's bounds are 64-bit terms, which nothing decides without
    // a fact context.
    if range.wide_bounds().is_some() {
        return false;
    }
    pointer_in_range_shallow(
        pointer,
        range.base(),
        range.start(),
        range.end(),
        range.element_width(),
        None,
    )
}

/// [`pointer_in_memory_range_shallow`] for a caller that does hold a fact
/// context, so a range whose start is only provably nonnegative still answers.
pub(in crate::kernel) fn pointer_in_memory_range_shallow_with_facts(
    pointer: &Address,
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // A wide range has one membership rule: the pointer addresses a whole
    // element at an unsigned 64-bit index inside the bounds.
    if range.wide_bounds().is_some() {
        return assumptions.pointer_access_in_wide_range(pointer, range.element_width(), range);
    }
    pointer_in_range_shallow(
        pointer,
        range.base(),
        range.start(),
        range.end(),
        range.element_width(),
        Some(assumptions),
    )
}

fn pointer_offsets_match_by_shallow_fact_graph(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (AddressOffset::Add(left_a, left_b), AddressOffset::Add(right_a, right_b)) => {
            pointer_offsets_match_by_shallow_fact_graph(left_a, right_a, assumptions)
                && pointer_offsets_match_by_shallow_fact_graph(left_b, right_b, assumptions)
        }
        (
            AddressOffset::Int32Scaled {
                value: left,
                byte_width: left_width,
            },
            AddressOffset::Int32Scaled {
                value: right,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && assumptions
                    .int32_values_known_equal_views(left.operand_view(), right.operand_view())
        }
        _ => false,
    }
}

fn pointer_in_memory_range_for_memory_resolution(
    pointer: &Address,
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // A wide range has its one membership rule.
    if range.wide_bounds().is_some() {
        return assumptions.pointer_access_in_wide_range(pointer, range.element_width(), range);
    }
    pointer_in_range_for_memory_resolution(
        pointer,
        range.base(),
        range.start(),
        range.end(),
        range.element_width(),
        assumptions,
    )
}

fn pointer_in_range_for_memory_resolution(
    pointer: &Address,
    base: &Address,
    start: &MachineTerm,
    end: &MachineTerm,
    element_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    if super::reasoning::resolution_interrupted() {
        return false;
    }
    let Some(pointer) =
        super::reasoning::pointer_in_block_for_memory_resolution(pointer, &base.base, assumptions)
    else {
        return false;
    };
    let pointer = &pointer;
    let Some(_query) = super::reasoning::ResolutionQueryGuard::enter(
        super::reasoning::ResolutionQuery::PointerInRange(
            pointer.clone(),
            base.clone(),
            start.clone(),
            end.clone(),
            element_width,
        ),
    ) else {
        return false;
    };
    // Every index collected here ends in a membership conclusion, so each is
    // the pointer's element delta exactly or not at all: `element_index_from_offset`
    // folds an exact `i64` byte offset into a wrapping 32-bit add, and a
    // residue read as an index is the wrap this rule cannot see.
    let mut indexes = pointer
        .exact_element_delta_from_base(base, element_width, Some(assumptions))
        .and_then(|delta| delta.as_index_term())
        .into_iter()
        .collect::<Vec<_>>();
    if let AddressOffset::Add(left, right) = &pointer.offset {
        crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "range membership: offset equality",
            || {
                if super::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
                    left,
                    &base.offset,
                    assumptions,
                ) && let Some(index) = exact_element_delta_from_offset(right, element_width)
                    .and_then(|delta| delta.as_index_term())
                    && !indexes.contains(&index)
                {
                    indexes.push(index);
                }
                if super::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
                    right,
                    &base.offset,
                    assumptions,
                ) && let Some(index) = exact_element_delta_from_offset(left, element_width)
                    .and_then(|delta| delta.as_index_term())
                    && !indexes.contains(&index)
                {
                    indexes.push(index);
                }
            },
        );
    }
    crate::instrumentation::measure_operation(
        "kernel",
        "explicit range arms",
        "range membership: index in range",
        || {
            indexes.iter().any(|index| {
                bitvector_index_in_range_shallow_views(
                    index.operand_view(),
                    MachineOperandView::Legacy(start),
                    MachineOperandView::Legacy(end),
                    assumptions,
                )
            })
        },
    )
}

/// Pins a term to a signed constant using EXACT facts only: either the term
/// is itself constant, or one recorded exact equality names its value. Exact
/// condition facts are pinned verbatim into certificates, so both smart
/// execution and check see the same set and the answer is deterministic.
/// One hop, no recursion: a value-dependent range endpoint like
/// `owner->len` is separated from its constant by exactly the recorded
/// resource fact, never by a rewrite chain.
pub(in crate::kernel) fn exact_signed_constant(
    term: &MachineTerm,
    assumptions: &PureFactContext,
) -> Option<i64> {
    exact_signed_constant_view(MachineOperandView::Legacy(term), assumptions)
}

pub(in crate::kernel) fn exact_signed_constant_view(
    term: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> Option<i64> {
    if let Some(value) = signed_index_constant(term) {
        return Some(value);
    }
    // The first true equality, in fact order, that pins `term` to a
    // constant: one keyed lookup instead of a scan of every condition fact.
    crate::instrumentation::record_deterministic_work(1);
    let (_, constant) = assumptions
        .equality_graph
        .exact_literal_sources_view(term)?
        .iter()
        .next()?;
    #[cfg(test)]
    EXACT_CONSTANT_FACT_VISITS.with(|visits| visits.set(visits.get() + 1));
    Some(*constant)
}

/// The constant an exact equality's other side names, read the way
/// [`exact_signed_constant`] reads it: signed 32-bit, then 64-bit signed,
/// then 64-bit unsigned when it fits.
fn exact_equality_constant(candidate: MachineOperandView<'_>) -> Option<i64> {
    candidate
        .word32_constant()
        .map(|value| i64::from(value as i32))
        .or_else(|| candidate.int64_constant())
        .or_else(|| {
            candidate
                .uint64_constant()
                .and_then(|value| i64::try_from(value).ok())
        })
}

/// [`exact_signed_constant`] for a term whose *sixty-four-bit* value is the
/// question — the value an `Int64Scaled` displacement scales.
///
/// A thirty-two-bit fact names a thirty-two-bit value and says nothing about
/// the other word, so it may not answer here: a low word of `0xFFFFFFFF` is
/// `-1`, and is equally `4294967295`, and is equally `2^32 + 4294967295`.
/// `exact_signed_constant` accepts one, which is right for the thirty-two-bit
/// quantities it was written for and wrong for this one. Only a sixty-four-bit
/// constant term, or arithmetic established through recorded exact
/// sixty-four-bit equalities, pins a value here.
///
/// `unsigned` says how the scaling reads it, and the two readings are
/// different numbers: `size_t` `4294967295` displaces forwards by that many
/// elements, while the same word read signed is the element below the base.
#[cfg(test)]
pub(in crate::kernel) fn exact_sixty_four_bit_constant(
    term: &MachineTerm,
    unsigned: bool,
    assumptions: &PureFactContext,
) -> Option<i64> {
    exact_sixty_four_bit_constant_view(MachineOperandView::Legacy(term), unsigned, assumptions)
}

pub(in crate::kernel) fn exact_sixty_four_bit_constant_view(
    term: MachineOperandView<'_>,
    unsigned: bool,
    assumptions: &PureFactContext,
) -> Option<i64> {
    let literal = if unsigned {
        term.uint64_constant()
            .and_then(|value| i64::try_from(value).ok())
    } else {
        term.int64_constant()
    };
    if let Some(value) = literal {
        return Some(value);
    }
    let bits = assumptions.wide_constant_from_equalities_view(term)?;
    if unsigned {
        i64::try_from(bits).ok()
    } else {
        Some(bits as i64)
    }
}

/// Exact constants for the two offset forms admitted by wide constant
/// congruence. Scaling must fit the offset's signed 64-bit representation.
pub(in crate::kernel) fn exact_wide_scaled_offset_constant(
    offset: &AddressOffset,
    assumptions: &PureFactContext,
) -> Option<i64> {
    match offset {
        AddressOffset::Constant(value) => Some(*value),
        AddressOffset::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => {
            let view = value.operand_view();
            let literal = if *unsigned {
                view.uint64_constant().and_then(|n| i64::try_from(n).ok())
            } else {
                view.int64_constant()
            };
            let number = literal.or_else(|| {
                let bits = assumptions.wide_constant_from_equalities_view(view)?;
                if *unsigned {
                    i64::try_from(bits).ok()
                } else {
                    Some(bits as i64)
                }
            })?;
            number.checked_mul(*byte_width)
        }
        _ => None,
    }
}

#[cfg(test)]
pub(in crate::kernel) fn bitvector_index_in_range_shallow(
    index: &MachineTerm,
    start: &MachineTerm,
    end: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    bitvector_index_in_range_shallow_views(
        MachineOperandView::Legacy(index),
        MachineOperandView::Legacy(start),
        MachineOperandView::Legacy(end),
        assumptions,
    )
}

pub(in crate::kernel) fn bitvector_index_in_range_shallow_views(
    index: MachineOperandView<'_>,
    start: MachineOperandView<'_>,
    end: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    let recorded_exact_order_path =
        |left: MachineOperandView<'_>, right: MachineOperandView<'_>, strict: bool| {
            let Some(path) = assumptions.exact_signed_order_source_path(left, right, strict) else {
                return false;
            };
            for step in path {
                record_implicit_consulted_premises(assumptions, &step.premise);
            }
            true
        };
    if let (Some(index), Some(start), Some(end)) = (
        signed_index_constant(index),
        signed_index_constant(start),
        signed_index_constant(end),
    ) {
        return start <= index && index < end;
    }
    // Value-dependent endpoints pinned by exact facts (e.g. a range end of
    // `owner->len` with the recorded exact fact `owner->len == 1`) resolve
    // to constants without any non-exact condition reasoning. Success only:
    // an unresolved or unsatisfied triple falls through to the other arms.
    if let (Some(index), Some(start), Some(end)) = (
        exact_signed_constant_view(index, assumptions),
        exact_signed_constant_view(start, assumptions),
        exact_signed_constant_view(end, assumptions),
    ) && start <= index
        && index < end
    {
        return true;
    }
    let lower_bound_is_exact = assumptions.selected_comparison_value(
        &index_comparison(CompareRelation::LessEqual, start, index),
    ) == Some(true)
        // Canonical-keyed bound lookup before any searching arm: indexed
        // and deterministic, so check sees the same answer.
        || assumptions.canonical_bound_holds_views(start, index, false)
        || recorded_exact_order_path(start, index, false)
        || assumptions.should_defer_non_exact_condition_reasoning()
            && assumptions.difference_graph_proves_order_views(start, index, false)
        || start.word32_constant() == Some(0)
            && index.int32_add_const_parts().is_some_and(|(base, increment)| {
                (increment as i32) > 0
                    && (recorded_exact_order_path(start, base, false)
                        || assumptions.should_defer_non_exact_condition_reasoning()
                            && assumptions
                                .difference_graph_proves_order_views(start, base, false))
                    && (held_index_add_nonoverflow(assumptions, base, MachineOperandView::Legacy(&MachineTerm::constant(increment)))
                        || held_index_add_nonoverflow(assumptions, MachineOperandView::Legacy(&MachineTerm::constant(increment)), base)
                        // A recorded strict signed upper bound (`base < y`)
                        // pins `base < INT_MAX`, so `base + 1` cannot
                        // overflow. Exact facts only; extended-bridging
                        // scope only, to keep every other phase's range
                        // answers byte-identical to the pre-arc path.
                        || increment == 1
                            && super::api::extended_dag_bridging_active()
                            && assumptions.has_exact_strict_upper_bound_view(base))
            });
    let upper_bound_is_exact = assumptions.selected_comparison_value(&index_comparison(
        CompareRelation::LessThan,
        index,
        end,
    )) == Some(true)
        || assumptions.canonical_bound_holds_views(index, end, true)
        || recorded_exact_order_path(index, end, true)
        || assumptions.should_defer_non_exact_condition_reasoning()
            && assumptions.difference_graph_proves_order_views(index, end, true);
    if lower_bound_is_exact && upper_bound_is_exact {
        // The bounds were read off exact facts along some indexed path; a
        // consulted-premise collection wants the facts behind them, whichever arm
        // found them.
        record_implicit_consulted_premises(
            assumptions,
            &Proposition::condition_is(
                index_comparison(CompareRelation::LessEqual, start, index),
                true,
            ),
        );
        record_implicit_consulted_premises(
            assumptions,
            &Proposition::condition_is(
                index_comparison(CompareRelation::LessThan, index, end),
                true,
            ),
        );
        return true;
    }

    element_delta_in_range_by_affine_arithmetic_views(
        &ExactElementDelta {
            index: index.retain(MachineIntegerType::Int32),
            constant: 0,
        },
        start,
        end,
        assumptions,
    )
}

/// Whether an exact element delta lands inside `[start, end)`, by affine
/// arithmetic over the range's own endpoints.
///
/// This is the tail of [`bitvector_index_in_range_shallow`], over a delta
/// rather than one index term, because a pointer's delta is an `i64` constant
/// beside a symbolic index and joining the two would need the modular add this
/// rule must not trust. The arms above that tail state the index as a term, so
/// they answer only for a delta that *is* one term
/// ([`ExactElementDelta::as_index_term`]); this one answers for both.
///
/// The affine routes read a constant difference as a signed order, and a
/// difference of modular terms is the true one only modulo `2^32`. An
/// "outside" conclusion survives that reduction — a residue past the count is
/// outside whichever way the terms wrapped — and "inside" does not, so the
/// offset here is the real one ([`exact_affine_index_difference_views`]) and the
/// length is the real element count ([`affine_range_element_count`]), or this
/// concludes nothing. The remaining arm compares the offset against the
/// range's length as a *term*, which is a signed order over that term's value
/// and needs no count.
pub(in crate::kernel) fn element_delta_in_range_by_affine_arithmetic(
    delta: &ExactElementDelta,
    start: &MachineTerm,
    end: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    element_delta_in_range_by_affine_arithmetic_views(
        delta,
        MachineOperandView::Legacy(start),
        MachineOperandView::Legacy(end),
        assumptions,
    )
}

pub(in crate::kernel) fn element_delta_in_range_by_affine_arithmetic_views(
    delta: &ExactElementDelta,
    start: MachineOperandView<'_>,
    end: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    let recorded_exact_order_path =
        |left: MachineOperandView<'_>, right: MachineOperandView<'_>, strict: bool| {
            let Some(path) = assumptions.exact_signed_order_source_path(left, right, strict) else {
                return false;
            };
            for step in path {
                record_implicit_consulted_premises(assumptions, &step.premise);
            }
            true
        };
    let Some(offset) =
        exact_affine_index_difference_views(delta.index.operand_view(), start, Some(assumptions))
            .and_then(|difference| difference.checked_add(delta.constant))
    else {
        return false;
    };
    if offset < 0 {
        return false;
    }
    if let Some(count) = affine_range_element_count_views(start, end) {
        return offset < count;
    }
    i32::try_from(offset).is_ok_and(|offset| {
        affine_bitvector_difference_atom_views(end, start).is_some_and(|length| {
            recorded_exact_order_path(
                MachineOperandView::Legacy(&MachineTerm::constant(offset as u32)),
                length.operand_view(),
                true,
            ) || assumptions.should_defer_non_exact_condition_reasoning()
                && assumptions.difference_graph_proves_order_views(
                    MachineOperandView::Legacy(&MachineTerm::constant(offset as u32)),
                    length.operand_view(),
                    true,
                )
        })
    })
}

/// An upper bound on the number of elements `start..end` can really span, for
/// a rule about to read an affine constant difference as an order.
///
/// [`affine_bitvector_difference_constant`] computes in `i64` while its
/// arguments are modular 32-bit terms, so what it returns is the true
/// difference only *modulo* `2^32`. That is enough for a disequality — the
/// residue is nonzero — and not enough for an order: `i + 1` is one above `i`
/// only while the 32-bit add does not wrap. What an order conclusion can still
/// get from a residue is membership, because an index whose residue from the
/// range's start is at least the range's element count is outside the range
/// whichever way the terms wrapped. That needs the count bounded, and this is
/// the bound.
///
/// Two sources, in order of cost. A constant affine element count *is* the
/// count when it sits in `0..=i32::MAX`, so the ordinary shapes — `p[i..i + 1]`,
/// `p[0..3]` — carry their own bound and consult nothing. Otherwise the range's
/// own valid-byte-span facts supply it, which is the condition a stated
/// `owns`/`views` range already brings. A range with neither is refused:
/// default-deny, since an unbounded span admits a residue that wrapped all the
/// way around.
pub(in crate::kernel) fn affine_range_element_count_bound(
    start: &MachineTerm,
    end: &MachineTerm,
    element_width: u32,
    assumptions: &PureFactContext,
) -> Option<i64> {
    if let Some(count) = affine_bitvector_difference_constant(end, start)
        && (0..=i64::from(i32::MAX)).contains(&count)
    {
        return Some(count);
    }
    assumptions.established_range_element_count_bound(start, end, element_width)
}

/// The number of elements a range spans, when its endpoints' affine difference
/// determines it. This is the count itself, not a bound.
///
/// A range `p[start..end)` denotes `memory_range_byte_count` bytes from the
/// address of element `start`, and that byte count is the modular term
/// `(end - start) * width`. So the element count is the *signed* value of the
/// 32-bit term `end - start`, which is the residue of an affine constant
/// difference read as `int32` — exactly, with nothing assumed: the affine walk
/// is faithful modulo `2^32`, and modulo `2^32` is all the count is. A residue
/// in the upper half is a negative count, a reversed range that holds no cells
/// and fails its own valid-span guard, and this answers `None` for it rather
/// than a count no conclusion should use.
///
/// Contrast [`affine_range_element_count_bound`], which answers for a range
/// whose endpoints have *no* constant difference by consulting its span
/// facts. A bound is all an "outside" conclusion needs; a membership
/// conclusion needs the count.
pub(in crate::kernel) fn affine_range_element_count(
    start: &MachineTerm,
    end: &MachineTerm,
) -> Option<i64> {
    let residue = affine_bitvector_difference_constant(end, start)?.rem_euclid(1i64 << 32);
    (residue < (1i64 << 31)).then_some(residue)
}

/// Whether a range's element count is a real count and not a residue standing
/// for a negative span — `0 <= end - start`, the forward half of the one
/// valid-byte-span condition, which is all this needs and the width limit is
/// not part of.
///
/// This is the premise for comparing two ranges' *ends* rather than their
/// counts. Write `offset` for how far the child starts into the parent and
/// `slack` for how far the parent's end reaches past the child's; both are
/// exact `i64`, and whatever the endpoints did,
/// `parent_count - child_count ≡ offset + slack (mod 2^32)`. Both counts are
/// residues read as `int32`, so they lie in `[-2^31, 2^31)`; a *nonnegative*
/// parent count puts their difference in `(-2^31, 2^32)`, and `offset + slack`
/// in `[0, 2^31)` is then the only value in that window congruent to it. So
/// the difference *is* `offset + slack`, and `slack >= 0` is exactly
/// `offset + child_count <= parent_count`.
///
/// Without it a range may be forward and valid with its endpoints nowhere near
/// each other: `p[i32::MAX..i32::MIN]` holds exactly one element, and reading
/// its `end` as `start + count` would place that element `2^32` away.
///
/// A reach of zero needs nothing at all: the two ranges then start at one
/// address and end at one address, so their counts are residues of the same
/// value and are equal.
// Exact-arithmetic containment handles wide ranges before calling this helper.
fn range_count_is_nonnegative(range: &MemoryRange, assumptions: Option<&PureFactContext>) -> bool {
    if affine_range_element_count(range.start(), range.end()).is_some() {
        return true;
    }
    assumptions.is_some_and(|assumptions| {
        assumptions.proves_element_endpoint_order(
            &MachineTerm::constant(0),
            &crate::kernel::memory_range_element_count(range),
        )
    })
}

/// Whether an affine constant difference from a range's start places the index
/// outside a range spanning at most `count_bound` elements.
///
/// The difference is the true one modulo `2^32`; taking its residue, the index
/// sits `residue` elements above the start or `residue - 2^32` below it. The
/// second is negative, so below the start either way; the first is outside once
/// it reaches the element count. A residue above any bound on that count is
/// therefore outside the range under both readings, with no no-overflow fact
/// needed.
fn affine_offset_from_start_is_outside(difference: i64, count_bound: i64) -> bool {
    difference.rem_euclid(1i64 << 32) > count_bound
}

/// Whether an affine constant difference from a range's *end* places the index
/// at or above the range, for a range spanning at most `count_bound` elements.
///
/// The index sits `residue` elements above the end, so its offset from the
/// start is `residue + count`. That stays at or above the count — outside —
/// unless it wraps, which it cannot while `residue + count` is below `2^32`.
fn affine_offset_from_end_is_outside(difference: i64, count_bound: i64) -> bool {
    difference.rem_euclid(1i64 << 32) < (1i64 << 32) - count_bound
}

fn bitvector_index_outside_range_shallow_view(
    index: MachineOperandView<'_>,
    start: &MachineTerm,
    end: &MachineTerm,
    element_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    if let (Some(index), Some(start), Some(end)) = (
        signed_index_constant(index),
        signed_bitvector_constant(start),
        signed_bitvector_constant(end),
    ) {
        return index < start || end <= index;
    }
    if assumptions.selected_comparison_value(&index_comparison(
        CompareRelation::LessThan,
        index,
        MachineOperandView::Legacy(start),
    )) == Some(true)
        || assumptions.has_exact_order_path_views(index, MachineOperandView::Legacy(start), true)
        || assumptions.selected_comparison_value(&index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(end),
            index,
        )) == Some(true)
        || assumptions.has_exact_order_path_views(MachineOperandView::Legacy(end), index, false)
    {
        return true;
    }
    // The affine routes read a constant difference as a signed order, which it
    // is not: the terms are modular, so the difference is the true one only
    // modulo 2^32. What survives is membership, against a bound on how far the
    // range reaches; without such a bound this concludes nothing.
    let Some(count_bound) =
        affine_range_element_count_bound(start, end, element_width, assumptions)
    else {
        return false;
    };
    affine_bitvector_difference_constant_views(index, MachineOperandView::Legacy(start))
        .is_some_and(|offset| affine_offset_from_start_is_outside(offset, count_bound))
        || affine_bitvector_difference_constant_views(index, MachineOperandView::Legacy(end))
            .is_some_and(|offset| affine_offset_from_end_is_outside(offset, count_bound))
}

/// Whether a pointer addresses one of the cells of `base[start..end)`, from
/// arithmetic alone, plus `assumptions` when the caller holds a context.
///
/// This is a membership conclusion, so every quantity it compares has to be the
/// real one. A range denotes `count` elements from the address of element
/// `start`, and the pointer names the address `base + delta * width`, so what
/// membership means is the `i64` statement `0 <= delta - sext(start) < count`.
/// Each of the three pieces is read exactly:
/// [`Address::exact_element_delta_from_base`] for `delta`, so a folded sum of
/// byte offsets cannot pass off a residue as one;
/// [`exact_affine_index_difference_views`] for the subtraction, which is where the
/// wrap that `p[i..i + 1]` hides at `i == i32::MAX` would be; and
/// [`affine_range_element_count`] for the count.
fn pointer_in_range_shallow(
    pointer: &Address,
    base: &Address,
    start: &MachineTerm,
    end: &MachineTerm,
    element_width: u32,
    assumptions: Option<&PureFactContext>,
) -> bool {
    let Some(delta) = pointer.exact_element_delta_from_base(base, element_width, assumptions)
    else {
        return false;
    };
    // A zero-based symbolic range needs no affine constant count: its
    // signed endpoint is its count. Exact bounds put the unshifted index
    // inside it, and the span guard prevents byte scaling from wrapping.
    // Keep nonzero starts and displacements on the exact-affine route below;
    // turning their modular sums into signed offsets would need more evidence.
    if start == &MachineTerm::constant(0)
        && delta.constant == 0
        && let Some(assumptions) = assumptions
        && assumptions
            .established_range_element_count_bound(start, end, element_width)
            .is_some()
        && let Some(lower) = assumptions.exact_direct_order_source_step(
            MachineOperandView::Legacy(start),
            delta.index.operand_view(),
            false,
        )
        && let Some(upper) = assumptions.exact_direct_order_source_step(
            delta.index.operand_view(),
            MachineOperandView::Legacy(end),
            true,
        )
    {
        record_implicit_consulted_premises(assumptions, &lower.premise);
        record_implicit_consulted_premises(assumptions, &upper.premise);
        return true;
    }
    let Some(count) = affine_range_element_count(start, end) else {
        return false;
    };
    let Some(offset) = exact_affine_index_difference_views(
        delta.index.operand_view(),
        MachineOperandView::Legacy(start),
        assumptions,
    )
    .and_then(|difference| difference.checked_add(delta.constant)) else {
        return false;
    };
    0 <= offset && offset < count
}

pub(in crate::kernel) fn affine_bitvector_difference_constant(
    left: &MachineTerm,
    right: &MachineTerm,
) -> Option<i64> {
    let mut terms = BTreeMap::new();
    let mut constant = 0i64;
    collect_affine_bitvector_terms(left, 1, &mut terms, &mut constant)?;
    collect_affine_bitvector_terms(right, -1, &mut terms, &mut constant)?;
    terms.retain(|_, coefficient| *coefficient != 0);
    terms.is_empty().then_some(constant)
}

fn collect_affine_bitvector_terms(
    term: &MachineTerm,
    coefficient: i64,
    terms: &mut BTreeMap<MachineTerm, i64>,
    constant: &mut i64,
) -> Option<()> {
    match term {
        bits32_constant!(value) => {
            *constant = constant
                .checked_add(coefficient.checked_mul(i64::from(constant_u32(*value) as i32))?)?;
        }
        binary_term!(Int32, Add, left, right) => {
            collect_affine_bitvector_terms(left, coefficient, terms, constant)?;
            collect_affine_bitvector_terms(right, coefficient, terms, constant)?;
        }
        binary_term!(Int32, Subtract, left, right) => {
            collect_affine_bitvector_terms(left, coefficient, terms, constant)?;
            collect_affine_bitvector_terms(right, coefficient.checked_neg()?, terms, constant)?;
        }
        binary_term!(Int32, Multiply, left, right) => {
            if let Some(value) = left.as_const() {
                collect_affine_bitvector_terms(
                    right,
                    coefficient.checked_mul(i64::from(value as i32))?,
                    terms,
                    constant,
                )?;
            } else {
                let value = right.as_const()?;
                collect_affine_bitvector_terms(
                    left,
                    coefficient.checked_mul(i64::from(value as i32))?,
                    terms,
                    constant,
                )?;
            }
        }
        atom => {
            // Atoms are keyed by their canonical form, so a load term and
            // its load variable cancel affinely; the verdict
            // stays assumption-free and check-identical because the
            // canonical form is deterministic.
            let current = terms
                .entry(crate::kernel::eval::canonical_term(atom))
                .or_default();
            *current = current.checked_add(coefficient)?;
        }
    }
    Some(())
}

impl ProofObligation {
    /// The ordinary indexed check for an evaluation requirement. Scoped
    /// quantifiers are discharged by proof operations, never by searching
    /// ambient quantified premises here.
    pub(crate) fn evaluation_requirement_is_established(
        assumptions: &PureFactContext,
        goal: &Proposition,
    ) -> bool {
        // Lowering can guard a native int32 universal's partial operation
        // with its own domain. Preserve only that existing reflexive route:
        // other binder sorts have distinct obligations, and logical
        // reflexivity must not erase a partial free expression's domain.
        fn reflexive_guard(goal: &Proposition) -> bool {
            let mut pending = vec![goal];
            while let Some(goal) = pending.pop() {
                crate::instrumentation::record_deterministic_work(1);
                match goal {
                    Proposition::ForAll {
                        sort: Sort::ProgramInt32,
                        body,
                        ..
                    } => pending.push(body),
                    Proposition::And(left, right) => {
                        pending.extend([left.as_ref(), right.as_ref()])
                    }
                    Proposition::Implies(left, right) if left == right => {}
                    _ => return false,
                }
            }
            true
        }
        fn established(assumptions: &PureFactContext, goal: &Proposition) -> bool {
            // Arithmetic domains are two ordinary bounds. Keep checking
            // them independently, using direct fact membership and the same
            // atomic query as the generic conjunction route below. No bound
            // needs the ambient alpha-equivalence index to be built first.
            if crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(goal)
                .is_some()
            {
                let Proposition::And(first, second) = goal else {
                    unreachable!("ordinary arithmetic domains are pairs of bounds");
                };
                let established_bound = |bound: &Proposition| {
                    assumptions
                        .contains_assumed_exact(&crate::kernel::canonical_condition_fact(bound))
                        || assumptions.proves_atomic_without_search(bound)
                };
                return established_bound(first) && established_bound(second);
            }
            if assumptions.states_required_goal(goal) || reflexive_guard(goal) {
                return true;
            }
            match goal {
                Proposition::And(left, right) => {
                    established(assumptions, left) && established(assumptions, right)
                }
                Proposition::ForAll { .. } | Proposition::Exists { .. } => false,
                _ => assumptions.proves_atomic_without_search(goal),
            }
        }
        established(assumptions, goal)
    }

    pub fn new(proposition: Proposition) -> Self {
        Self {
            proposition,
            context: None,
            assumable: true,
            evaluation_domain: false,
            assertion_failure: false,
            call_requirement_site: None,
            introductions: None,
        }
    }

    pub fn verification_condition(proposition: Proposition) -> Self {
        Self {
            // A condition the kernel builds, such as a ranking decrease over
            // an Integer measure, is stated in the same one form as written
            // ones.
            proposition: canonical_observation_form(&proposition),
            context: None,
            assumable: false,
            evaluation_domain: false,
            assertion_failure: false,
            call_requirement_site: None,
            introductions: None,
        }
    }

    pub(in crate::kernel) fn evaluation_domain(proposition: Proposition) -> Self {
        let mut obligation = Self::verification_condition(proposition);
        obligation.evaluation_domain = true;
        obligation
    }

    pub(in crate::kernel) fn with_assertion_failure(mut self) -> Self {
        self.assertion_failure = true;
        self
    }

    pub(crate) fn is_assertion_failure(&self) -> bool {
        self.assertion_failure
    }

    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    /// Attaches the head chain the lowering that produced this obligation's
    /// proposition recorded for it. One `Arc` clone per obligation copy; the
    /// chain itself is never rebuilt or scanned here.
    pub(super) fn with_introductions(
        mut self,
        introductions: crate::kernel::LoweringIntroductions,
    ) -> Self {
        self.introductions = Some(std::sync::Arc::new(introductions));
        self
    }

    /// The same chain, shared. Used when one obligation's record is carried
    /// onto the copy another collector keeps.
    pub(super) fn with_shared_introductions(
        mut self,
        introductions: Option<&std::sync::Arc<crate::kernel::LoweringIntroductions>>,
    ) -> Self {
        self.introductions = introductions.cloned();
        self
    }

    /// What lowering recorded about this obligation's outermost nodes, when
    /// a lowering built it. Indexed access by the consumer; no scan here.
    pub fn introductions(&self) -> Option<&crate::kernel::LoweringIntroductions> {
        self.introductions.as_deref()
    }

    /// The exact source-side identity for a required call precondition, when
    /// this obligation came from a selected callee contract.
    pub(crate) fn call_requirement_site(&self) -> Option<&std::sync::Arc<CallRequirementSource>> {
        self.call_requirement_site.as_ref()
    }

    /// Attach source-side call identity without changing the checked
    /// proposition identity used by obligation indexes.
    pub(crate) fn with_call_requirement_site(
        mut self,
        site: std::sync::Arc<CallRequirementSource>,
    ) -> Self {
        self.call_requirement_site = Some(site);
        self
    }

    pub(super) fn shared_introductions(
        &self,
    ) -> Option<&std::sync::Arc<crate::kernel::LoweringIntroductions>> {
        self.introductions.as_ref()
    }

    /// Whether this obligation is the impossible goal `false = true` the
    /// kernel owes where something is already refused. Its context is then
    /// the whole reason, and a caller whose proof of it failed reports that
    /// context instead of the attempt.
    pub fn is_impossible_goal(&self) -> bool {
        self.proposition == crate::kernel::loops::false_equals_true_proposition()
    }

    pub fn is_assumable(&self) -> bool {
        self.assumable
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::condition_is(condition, value))
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }

    pub(super) fn map_proposition(self, f: impl FnOnce(Proposition) -> Proposition) -> Self {
        Self {
            proposition: f(self.proposition),
            context: self.context,
            assumable: self.assumable,
            evaluation_domain: self.evaluation_domain,
            assertion_failure: self.assertion_failure,
            call_requirement_site: None,
            // The chain describes the head nodes of the proposition it was
            // recorded for. A rewrite adds or removes head nodes, so the
            // record is dropped rather than left describing another shape.
            introductions: None,
        }
    }
}

impl ExecutionPureFact {
    /// The value observed by this producer's completed volatile read.
    pub(crate) fn volatile_read_result(&self) -> Option<&ProgramValue> {
        crate::instrumentation::record_deterministic_work(1);
        if !self.is_certified() {
            return None;
        }
        let Proposition::VolatileAccess(event) = self.proposition() else {
            return None;
        };
        (event.kind == VolatileAccessKind::Read).then(|| event.value.native_compat())
    }

    pub(crate) fn volatile_read_retained_result(&self) -> Option<&crate::kernel::ExecutionValue> {
        crate::instrumentation::record_deterministic_work(1);
        if !self.is_certified() {
            return None;
        }
        let Proposition::VolatileAccess(event) = self.proposition() else {
            return None;
        };
        (event.kind == VolatileAccessKind::Read).then(|| event.value.value())
    }

    /// Retain the exact typed producer's definition and checked cached value.
    /// Used when a checked expression's value outlives its temporary fact
    /// stream (for example, an owned recursive child index). Definitions are
    /// unconditional; a cached value reached through an alias stays local to
    /// this proof context. Neither grants permission to read the cell.
    pub(in crate::kernel) fn retain_pointer_read_definition(&self, context: &PureFactContext) {
        if !self.is_certified() {
            return;
        }
        if let Some((value, memory, address)) = self.checked_pointer_read.as_deref() {
            context.register_checked_pointer_read(value, memory, address);
        }
        if self.is_logical_read_equation() {
            match self.proposition() {
                condition_source_0 @ Proposition::ConditionIs(_, true)
                    if let Some((ConditionTerm::PointerEqual(left, right), _)) =
                        condition_source_0.condition_native() =>
                {
                    context
                        .equality_graph
                        .add_checked_pointer_equality(left, right);
                    return;
                }
                // A complete value equation simplifies to address equality
                // when its provenance and bounds already match. Retain that
                // exact producer conclusion without adding object authority.
                condition_source_0 @ Proposition::ConditionIs(_, true)
                    if let Some((ConditionTerm::AddressEqual(left, right), _)) =
                        condition_source_0.condition_native() =>
                {
                    context
                        .equality_graph
                        .add_checked_read_equality(left, right);
                    return;
                }
                _ => {}
            }
        }
        let Some(
            binding @ GeneratedLoadBinding::Exact {
                variable,
                pointer: address,
                load: MachineTerm::MemoryLoad(memory, _, _),
                typed_pointer_value: Some(value),
                observed_pointer_read,
                ..
            },
        ) = self.generated_load_binding()
        else {
            return;
        };
        if generated_load_binding_matches_proposition(binding, self.proposition())
            && crate::kernel::eval::typed_pointer_read_variable(value) == Some(*variable)
        {
            context.register_checked_pointer_read(value, memory.shared_memory(), address);
            if let Some((observed_memory, observed_address)) = observed_pointer_read {
                context.equality_graph.add_checked_read_equality(
                    value,
                    &Address::loaded_value(observed_memory, observed_address),
                );
            }
        }
    }

    pub fn new(proposition: Proposition) -> Self {
        Self::from_shared(std::sync::Arc::new(proposition))
    }

    pub(crate) fn from_shared(proposition: std::sync::Arc<Proposition>) -> Self {
        Self {
            proposition,
            public: true,
            certified: false,
            logical_read_equation: false,
            join_summary: false,
            resource_effect_bound: None,
            certified_store: None,
            transport: None,
            generated_load_binding: None,
            checked_pointer_read: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    pub(super) fn internal(proposition: Proposition) -> Self {
        Self {
            proposition: std::sync::Arc::new(proposition),
            public: false,
            certified: false,
            logical_read_equation: false,
            join_summary: false,
            resource_effect_bound: None,
            certified_store: None,
            transport: None,
            generated_load_binding: None,
            checked_pointer_read: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    /// The memory summary of a checked interface join: what the arms'
    /// effects, each already checked against its own chain, may have
    /// written between the split and the joined memory.
    ///
    /// A join's memory is its arms' abstraction, which also forgets values
    /// no arm wrote, so the summary cannot be derived again from its two
    /// endpoints the way a store's or a call's can. An enclosing join takes
    /// it as the checked fact it is.
    pub(super) fn certified_join_summary(proposition: Proposition) -> Self {
        Self {
            join_summary: true,
            resource_effect_bound: None,
            ..Self::certified(proposition)
        }
    }

    pub(crate) fn is_join_summary(&self) -> bool {
        self.certified && self.join_summary
    }

    pub(super) fn certified(proposition: Proposition) -> Self {
        Self {
            proposition: std::sync::Arc::new(proposition),
            public: true,
            certified: true,
            logical_read_equation: false,
            join_summary: false,
            resource_effect_bound: None,
            certified_store: None,
            transport: None,
            generated_load_binding: None,
            checked_pointer_read: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    pub(in crate::kernel) fn logical_read_equation(value: Pointer, read: Address) -> Self {
        let read = Pointer::new(read, value.program_type());
        Self::logical_pointer_value_equation(value, read)
    }

    pub(in crate::kernel) fn checked_pointer_read_equation(
        value: Pointer,
        observed: Address,
    ) -> Self {
        let evidence = value.address().as_loaded_value().map(|read| {
            Box::new((
                value.address().clone(),
                read.defining_memory,
                read.defining_address,
            ))
        });
        Self {
            checked_pointer_read: evidence,
            ..Self::logical_read_equation(value, observed)
        }
    }

    pub(crate) fn has_checked_pointer_read(&self) -> bool {
        self.checked_pointer_read.is_some()
    }

    pub(in crate::kernel) fn logical_pointer_value_equation(left: Pointer, right: Pointer) -> Self {
        Self {
            logical_read_equation: true,
            ..Self::certified(Proposition::condition_is(
                ConditionTerm::pointer_equal(left, right),
                true,
            ))
        }
    }

    pub(in crate::kernel) fn is_logical_read_equation(&self) -> bool {
        self.certified && self.logical_read_equation
    }

    pub(super) fn certified_store(
        before: SymbolicMemory,
        after: SymbolicMemory,
        pointer: Address,
        value: impl Into<StoredMemoryValue>,
        authorized_range: Option<MemoryRange>,
    ) -> Self {
        let value = value.into();
        let value_equation = super::memory_history::stored_value_equation(&after, &pointer, &value)
            .map(std::sync::Arc::new);
        Self {
            proposition: std::sync::Arc::new(Proposition::MemoryMutatesOnly {
                before: before.clone(),
                after: after.clone(),
                writes: vec![(pointer.clone(), value.byte_width())],
            }),
            public: false,
            certified: true,
            logical_read_equation: false,
            join_summary: false,
            resource_effect_bound: None,
            certified_store: Some(Box::new(CertifiedMemoryStore {
                value_equation,
                before,
                after,
                pointer,
                value,
                authorized_range,
                source: Default::default(),
                source_address: None,
            })),
            transport: None,
            generated_load_binding: None,
            checked_pointer_read: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    pub(super) fn into_certified(mut self) -> Self {
        self.certified = true;
        self
    }

    pub(crate) fn with_proposition(mut self, proposition: Proposition) -> Self {
        if self.proposition.as_ref() != &proposition
            || self.generated_load_binding.as_ref().is_some_and(|binding| {
                !generated_load_binding_matches_proposition(binding, &proposition)
            })
            || !self.reference_observation.matches_proposition(&proposition)
        {
            // A transported or rewritten fact no longer denotes the exact
            // producer equation.  Retaining its binding would let a later
            // surface consumer infer an epoch or pointer from a different
            // proposition.
            self.resource_effect_bound = None;
            self.logical_read_equation = false;
            self.generated_load_binding = None;
            self.checked_pointer_read = None;
            self.generated_load_source_events = Default::default();
            self.reference_observation = Default::default();
            if let Some(store) = &mut self.certified_store {
                store.source = Default::default();
                store.source_address = None;
            }
        }
        self.proposition = std::sync::Arc::new(proposition);
        self
    }

    pub(crate) fn with_generated_load_binding(mut self, binding: GeneratedLoadBinding) -> Self {
        self.generated_load_binding = Some(Box::new(binding));
        self
    }

    pub(crate) fn with_generated_load_source_event(
        mut self,
        event: GeneratedLoadSourceEvent,
    ) -> Self {
        self.generated_load_source_events.push(event);
        self
    }

    pub(crate) fn generated_load_source_events(&self) -> &[GeneratedLoadSourceEvent] {
        self.generated_load_source_events.as_slice()
    }

    pub(crate) fn certified_transport(
        source: Proposition,
        target: Proposition,
        theorem: Theorem,
    ) -> Self {
        Self {
            proposition: std::sync::Arc::new(target),
            public: false,
            certified: true,
            logical_read_equation: false,
            join_summary: false,
            resource_effect_bound: None,
            certified_store: None,
            transport: Some(Box::new(CertifiedExecutionFactTransport {
                source,
                theorem,
            })),
            generated_load_binding: None,
            checked_pointer_read: None,
            generated_load_source_events: Default::default(),
            reference_observation: Default::default(),
        }
    }

    pub(crate) fn transport_source(&self) -> Option<&Proposition> {
        self.transport.as_ref().map(|transport| &transport.source)
    }

    pub(crate) fn transport_theorem(&self) -> Option<&Theorem> {
        self.transport.as_ref().map(|transport| &transport.theorem)
    }

    pub(crate) fn generated_load_binding(&self) -> Option<&GeneratedLoadBinding> {
        self.generated_load_binding.as_deref()
    }

    pub fn condition(condition: ConditionTerm, value: bool) -> Self {
        Self::new(Proposition::condition_is(condition, value))
    }

    pub(crate) fn shared_proposition(&self) -> std::sync::Arc<Proposition> {
        self.proposition.clone()
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub(crate) fn is_public(&self) -> bool {
        self.public
    }

    pub(crate) fn is_certified(&self) -> bool {
        self.certified
    }

    pub(crate) fn certified_store_equation(&self) -> Option<&std::sync::Arc<Proposition>> {
        self.certified_store_data()?.value_equation.as_ref()
    }

    pub(crate) fn certified_store_source_address(&self) -> Option<&Address> {
        self.certified_store_data()?.source_address.as_ref()
    }

    pub(super) fn certified_store_data(&self) -> Option<&CertifiedMemoryStore> {
        self.certified_store.as_deref()
    }
}

/// A generated-load binding is valid only while its exact defining equation
/// names the producer's memory state, pointer, and kind, either through
/// its registered read handle or an exact raw descriptor. Structural equality
/// alone does not retain the memory epoch, so it cannot retain the binding.
fn generated_load_binding_matches_proposition(
    binding: &GeneratedLoadBinding,
    proposition: &Proposition,
) -> bool {
    let GeneratedLoadBinding::Exact {
        variable,
        retained_state,
        pointer,
        load,
        ..
    } = binding
    else {
        return true;
    };
    let Some((
        ConditionTerm::Compare {
            format: _,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    )) = proposition.condition_native()
    else {
        return false;
    };
    let MachineTerm::Variable(proposition_variable) = left.as_ref() else {
        return false;
    };
    if proposition_variable != variable {
        return false;
    }
    match right.as_ref() {
        MachineTerm::MemoryLoad(memory, proposition_pointer, _) => {
            retained_state == &MemoryStateIdentity::of(memory.memory())
                && proposition_pointer.as_ref() == pointer
                && load == right.as_ref()
        }
        MachineTerm::Variable(read) => {
            // The source-level read uses its registered handle. Compare its
            // descriptor by indexed lookup, retaining exact epoch and width;
            // no equality facts can authorize this producer metadata.
            let Some(MachineTerm::MemoryLoad(memory, address, kind)) =
                crate::kernel::registered_load_term_for_variable(read)
            else {
                return false;
            };
            retained_state == &MemoryStateIdentity::of(memory.memory())
                && address.as_ref() == pointer
                && matches!(load, MachineTerm::MemoryLoad(_, _, expected) if *expected == kind)
        }
        _ => false,
    }
}

impl SymbolicExecution {
    pub fn paths(&self) -> &[SymbolicExecutionPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicExecutionPath {
    pub(crate) fn call_result(&self) -> Option<&StoredExecutionValue> {
        self.call_result.as_ref()
    }

    /// The callee's by-value aggregate parameters as this path's call bound
    /// them, when it is such a call.
    pub(crate) fn call_parameters(&self) -> Option<&CallParameters> {
        self.call_parameters.as_ref()
    }

    /// The entry premises this path was checked under.
    pub fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    pub fn facts(&self) -> &ExecutionFacts {
        &self.facts
    }

    pub fn execution_facts(&self) -> ExecutionFacts {
        let mut facts = self.facts.clone();
        let effects = self.effect_facts.filtered(|fact| !facts.contains(fact));
        facts.extend_shared(&effects);
        facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub(crate) fn loan_evidence(&self) -> &crate::kernel::loans::CheckedLoanCallEvidenceSequence {
        &self.loan_evidence
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

impl FunctionExecutionCandidates {
    pub fn state(&self) -> &ExecutionState {
        &self.data.state
    }

    pub fn function(&self) -> &ProgramFunction {
        &self.data.function
    }

    pub fn arguments(&self) -> &[ProgramExpression] {
        &self.data.arguments
    }

    pub(crate) fn candidate_at(&self, index: usize) -> Option<&FunctionExecutionCandidate> {
        self.data.paths.get(index)
    }
    pub(crate) fn path_count(&self) -> usize {
        self.data.paths.len()
    }
    pub(crate) fn common_facts_contain(&self, fact: &ExecutionPureFact) -> bool {
        self.data
            .common_facts
            .as_ref()
            .is_some_and(|facts| facts.contains(fact))
    }

    pub fn paths(&self) -> &[FunctionExecutionCandidate] {
        self.data.paths.as_slice_with(|paths| {
            #[cfg(test)]
            ExecutionFacts::record_published_storage(
                false,
                paths.len(),
                paths
                    .iter()
                    .flat_map(|path| [path.facts(), path.effect_facts()]),
            );
            #[cfg(not(test))]
            let _ = paths;
        })
    }
}

#[cfg(test)]
thread_local! {
    static MATERIALIZED_EXECUTION_FACTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many facts [`FunctionExecutionCandidate::execution_facts`] has
/// merged into fresh streams on this thread.
#[cfg(test)]
pub(crate) fn materialized_execution_facts() -> usize {
    MATERIALIZED_EXECUTION_FACTS.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(crate) fn count_materialized_execution_facts(count: usize) {
    MATERIALIZED_EXECUTION_FACTS.with(|counter| counter.set(counter.get() + count));
}

impl FunctionExecutionCandidate {
    pub(crate) fn shares_record_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.data, &other.data)
    }
    pub fn outcome(&self) -> &FunctionOutcome {
        &self.data.outcome
    }

    pub fn facts(&self) -> &ExecutionFacts {
        &self.data.facts
    }

    pub fn effect_facts(&self) -> &ExecutionFacts {
        &self.data.effect_facts
    }

    pub fn execution_facts(&self) -> ExecutionFacts {
        #[cfg(test)]
        count_materialized_execution_facts(self.data.facts.len() + self.data.effect_facts.len());
        let mut facts = self.data.facts.clone();
        let effects = self
            .data
            .effect_facts
            .filtered(|fact| !facts.contains(fact));
        facts.extend_shared(&effects);
        facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.data.obligations
    }

    pub(crate) fn loan_evidence(&self) -> &crate::kernel::loans::CheckedLoanCallEvidenceSequence {
        &self.data.loan_evidence
    }
}

impl SymbolicConditionEvaluation {
    pub fn paths(&self) -> &[SymbolicConditionEvaluationPath] {
        &self.paths
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.limit
    }
}

impl SymbolicConditionEvaluationPath {
    /// What the condition evaluates to on this path.
    pub fn outcome(&self) -> &ConditionOutcome {
        &self.outcome
    }

    pub fn facts(&self) -> &ExecutionFacts {
        &self.facts
    }

    pub fn obligations(&self) -> &[ProofObligation] {
        &self.obligations
    }

    pub fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

#[cfg(test)]
mod stated_requirement_tests {
    use super::*;

    fn requirement(var: u64, name: &str) -> Proposition {
        Proposition::Exists {
            name: name.into(),
            var: Variable(var),
            sort: Sort::Bitvector32,
            body: Box::new(Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(MachineTerm::Variable(Variable(var))),
                    right: Box::new(MachineTerm::constant(4)),
                },
                true,
            )),
        }
    }

    #[test]
    fn stated_quantified_requirement_survives_alpha_renaming_and_restriction() {
        let fact = requirement(100, "fact");
        let renamed = requirement(200, "goal");
        let context = PureFactContext::new().assume_proposition(fact);
        assert!(context.states_required_goal(&renamed));
        assert!(
            !context
                .restricted_to_facts(&[], &[])
                .states_required_goal(&renamed)
        );

        let sibling = PureFactContext::new();
        assert!(!sibling.states_required_goal(&renamed));
        assert!(context.states_required_goal(&renamed));
    }

    #[test]
    fn stated_query_assembles_conjunction_but_not_disjunction() {
        let left = Proposition::condition_is(ConditionTerm::Constant(true), true);
        let right = Proposition::condition_is(ConditionTerm::Constant(false), false);
        let context = PureFactContext::new()
            .assume_proposition(left.clone())
            .assume_proposition(right.clone());
        let conjunction = Proposition::And(Box::new(left.clone()), Box::new(right.clone()));
        let disjunction = Proposition::Or(Box::new(left.clone()), Box::new(right.clone()));
        assert!(context.states_required_goal(&conjunction));
        assert!(!context.states_required_goal(&disjunction));
        let guarded = Proposition::Implies(Box::new(disjunction), Box::new(conjunction));
        assert!(context.states_required_goal(&guarded));
        assert!(!PureFactContext::new().states_required_goal(&guarded));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/stated_requirement_tests.rs");
    }
}

#[cfg(test)]
mod dynamic_current_load_tests {
    use super::*;

    fn pointer() -> Address {
        Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        }
    }

    #[test]
    fn records_unmaterialized_loads_and_integer_machine_carriers() {
        let pointer = pointer();
        let memory = SymbolicMemory::new();
        let retained_state = crate::kernel::intern_memory_ref(&memory);
        let load = MachineTerm::MemoryLoad(
            ProgramPoint::at(&retained_state),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let value = Term::ProgramValue(ProgramValue::Int64(load.clone()));
        assert_eq!(
            current_memory_loads_in_term(&value, &memory).unwrap(),
            vec![(pointer.clone(), 8)]
        );

        let integer = SharedIntegerTerm::intern(IntegerTerm::Machine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::Int64, load),
        ));
        let condition = Term::Condition(ConditionTerm::IntegerEqual(
            integer,
            SharedIntegerTerm::intern(IntegerTerm::constant_i64(0)),
        ));
        assert_eq!(
            current_memory_loads_in_term(&condition, &memory).unwrap(),
            vec![(pointer, 8)]
        );
    }

    fn conversion_root(
        payload: SharedIntegerTerm,
        format: MachineIntegerType,
    ) -> crate::kernel::KernelTerm {
        let payload = crate::kernel::KernelTermImport::default().integer(&payload);
        crate::kernel::KernelTerm::integer_to_machine(format, payload).unwrap()
    }

    fn observed(root: crate::kernel::KernelTerm, format: MachineIntegerType) -> Term {
        let value = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
        assert!(!value.has_boxed_operand());
        Term::Integer(IntegerTerm::Machine(value))
    }

    fn load_payload(memory: &SymbolicMemory, format: MachineIntegerType) -> SharedIntegerTerm {
        let load = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            format,
            MachineTerm::MemoryLoad(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
                Box::new(pointer()),
                crate::kernel::LoadKind::Int32,
            ),
        ))
        .into();
        // An Integer conditional has a retained Integer identity. A bare raw
        // machine load still has producer-local identity and correctly stays
        // outside the shared arithmetic storage fragment.
        IntegerTerm::If {
            condition: Box::new(ConditionTerm::Constant(true)),
            then_term: load,
            else_term: IntegerTerm::constant_i64(0).into(),
        }
        .into()
    }

    #[test]
    fn shared_conversion_loads_preserve_width_and_state_without_exports() {
        use crate::kernel::{KernelTerm, KernelTermExport, MachineBinaryOp, VerificationSession};
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::Int16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt64,
            MachineIntegerType::Int128,
        ] {
            let _session = VerificationSession::enter();
            let memory = SymbolicMemory::new();
            let other = memory
                .clone()
                .store(pointer(), ProgramValue::Int32(1u32.into()));
            let root = conversion_root(load_payload(&memory, format), MachineIntegerType::Int32);
            let root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
            let term = observed(root, MachineIntegerType::Int32);
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                current_memory_loads_in_term(&term, &memory).unwrap(),
                vec![(pointer(), format.format().byte_width())]
            );
            assert!(
                current_memory_loads_in_term(&term, &other)
                    .unwrap()
                    .is_empty()
            );
            // The intervening query must not cache the historical result.
            assert_eq!(
                current_memory_loads_in_term(&term, &memory).unwrap().len(),
                1
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn shared_conversion_keeps_opaque_memory_refusal() {
        use crate::kernel::{KernelTermExport, SharedPureApplication, VerificationSession};
        let _session = VerificationSession::enter();
        let payload = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "opaque".into(),
            vec![],
        ))
        .into();
        let term = observed(
            conversion_root(payload, MachineIntegerType::Int32),
            MachineIntegerType::Int32,
        );
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(
            current_memory_loads_in_term(&term, &SymbolicMemory::new()).unwrap_err(),
            "opaque integer function may hide a current memory load"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_fold_endpoints_keep_memory_dependencies() {
        use crate::kernel::{KernelTermExport, VerificationSession};
        let _session = VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let root = conversion_root(
            load_payload(&memory, MachineIntegerType::UInt64),
            MachineIntegerType::UInt64,
        );
        let endpoint = SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(995001)))
            .with_shared_operand(root.with_machine_observation_type(MachineIntegerType::Int32))
            .unwrap();
        assert!(!endpoint.machine_operand().has_boxed_operand());
        let exports = KernelTermExport::machine_export_count();
        let fold = Term::Integer(IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::UInt64 {
                start: endpoint.clone(),
                end: endpoint,
            },
            initial: IntegerTerm::constant_i64(0).into(),
            accumulator: Variable(995002),
            item: Variable(995003),
            body: IntegerTerm::constant_i64(0).into(),
        });
        assert_eq!(
            current_memory_loads_in_term(&fold, &memory).unwrap(),
            vec![(pointer(), 8)]
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    mod scaling_tests {
        use super::*;
        include!("../scaling_tests/kernel/assumptions/dynamic_current_load_tests.rs");
    }

    #[test]
    fn opaque_click_function_carrier_is_rejected() {
        let memory = SymbolicMemory::new();
        let term = Term::Bitvector32(MachineTerm::ClickFunctionApplication {
            name: "opaque".into(),
            arguments: Vec::new(),
        });
        assert!(current_memory_loads_in_term(&term, &memory).is_err());
    }
}

/// An arithmetic overflow question whose two operands are load variables
/// reading one cell, as `a -= a` reads `this->size` and `other.size` when
/// `other` is `*this`: the operands are one value, so the question is asked
/// of that value with itself. Two registry lookups, one pointer decision in
/// the graph, and exact cell lookups; nothing is searched.
fn aliased_operands(
    graph: &super::difference_graph::DifferenceGraph,
    condition: &ConditionTerm,
) -> Option<bool> {
    use ConditionTerm as C;
    let (ty, operation, a, b) =
        super::machine_integer::representation::overflow_operation(condition)?;
    let (MachineTerm::Variable(left), MachineTerm::Variable(right)) = (a, b) else {
        return None;
    };
    if left == right
        || !crate::kernel::eval::is_load_variable(left)
        || !crate::kernel::eval::is_load_variable(right)
        || crate::kernel::registered_load_kind_for_variable(left)?
            != crate::kernel::registered_load_kind_for_variable(right)?
    {
        return None;
    }
    let (left_memory, left_pointer) = crate::kernel::registered_load_for_variable(left)?;
    let (right_memory, right_pointer) = crate::kernel::registered_load_for_variable(right)?;
    let same_cell = graph.decide(&C::AddressEqual(
        Box::new(left_pointer.clone()),
        Box::new(right_pointer.clone()),
    )) == Some(true)
        || (left_pointer.base == right_pointer.base
            && graph.decide(&C::AddressOffsetEqual(
                Box::new(left_pointer.offset.clone()),
                Box::new(right_pointer.offset.clone()),
            )) == Some(true));
    // The two states agree at the cell when they are one state, or
    // when one materialized the other's read there (`this->size` read
    // first, then `other.size` from a state that records it): an exact
    // cell lookup each way.
    let holds = |memory: &SharedMemory, pointer: &Address, variable: &Variable| {
        matches!(
            memory.known_value(pointer),
            Some(ProgramValue::Int32(MachineTerm::Variable(held))
                | ProgramValue::Int64(MachineTerm::Variable(held))
                | ProgramValue::UInt64(MachineTerm::Variable(held))) if held == *variable
        )
    };
    if !same_cell
        || !(left_memory == right_memory
            || holds(&right_memory, &left_pointer, left)
            || holds(&left_memory, &right_pointer, right))
    {
        return None;
    }
    let itself = super::machine_integer::representation::overflow_condition(
        ty,
        operation,
        Box::new(a.clone()),
        Box::new(a.clone()),
    )?;
    graph.decide(&itself)
}

/// `proposition` with exact machine observations read in their native carrier.
/// Shared operands remain retained comparisons; this does not export their
/// arithmetic prefixes. A comparison whose native form folds to a constant,
/// such as a type-range bound, keeps its Integer form. The walk visits each
/// connective once and never consults facts.
pub(crate) fn canonical_observation_form(proposition: &Proposition) -> Proposition {
    observation_comparison_form(proposition)
}

fn observation_comparison_form(proposition: &Proposition) -> Proposition {
    crate::instrumentation::record_deterministic_work(1);
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            match super::machine_integer::comparison::structural_native_comparison_view(
                condition.native_compat(),
                *value,
            )
            .map(|view| view.retained_condition())
            {
                Some((ConditionTerm::Constant(_), _)) | None => proposition.clone(),
                Some((native, truth)) => Proposition::condition_is(native, truth),
            }
        }
        Proposition::Not(inner) => Proposition::Not(Box::new(observation_comparison_form(inner))),
        Proposition::And(left, right) => Proposition::And(
            Box::new(observation_comparison_form(left)),
            Box::new(observation_comparison_form(right)),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(observation_comparison_form(left)),
            Box::new(observation_comparison_form(right)),
        ),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(observation_comparison_form(left)),
            Box::new(observation_comparison_form(right)),
        ),
        other => other.clone(),
    }
}

/// The native comparison fact that an Integer comparison fact of exact
/// observations of one machine type holds exactly when it does
/// (`native_comparison_of_integer_observation`), or `None` for any other fact.
pub(crate) fn native_reading_of_integer_observation_fact(
    proposition: &Proposition,
) -> Option<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let (native, truth) =
        native_comparison_of_integer_observation(condition.native_compat(), *value)?;
    Some(Proposition::condition_is(native, truth))
}

/// The two spellings of one non-strict Integer order, `a <= b` and
/// `b >= a`; any other condition alone.
fn integer_order_spellings(condition: &ConditionTerm) -> Vec<ConditionTerm> {
    match condition {
        ConditionTerm::IntegerLessEqual(left, right) => vec![
            condition.clone(),
            ConditionTerm::IntegerGreaterEqual(right.clone(), left.clone()),
        ],
        ConditionTerm::IntegerGreaterEqual(left, right) => vec![
            condition.clone(),
            ConditionTerm::IntegerLessEqual(right.clone(), left.clone()),
        ],
        other => vec![other.clone()],
    }
}

#[cfg(test)]
mod integer_observation_tests {
    use super::*;
    use crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison;
    use crate::kernel::primitives::IntegerTerm;
    use num_bigint::BigInt;

    #[test]
    fn fresh_known_observation_lookups_keep_arithmetic_shared() {
        use crate::kernel::machine_integer::{
            Relation,
            comparison::{ComparisonOperand, NativeComparisonView},
        };
        use crate::kernel::{
            KernelTerm, KernelTermExport, KernelType, MachineBinaryOp as Op,
            SharedMachineIntegerTerm,
        };
        for relation in [
            Relation::Equal,
            Relation::NotEqual,
            Relation::Less,
            Relation::LessEqual,
        ] {
            let _session = crate::kernel::VerificationSession::enter();
            let ty = MachineIntegerType::Int32;
            let variable =
                |id| KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
            let root = KernelTerm::machine_binary_shared(
                ty,
                Op::Multiply,
                [variable(974001), variable(974002)],
            );
            let other = variable(974003);
            let read = NativeComparisonView {
                format: ty,
                relation,
                operands: [root, other].map(|root| {
                    ComparisonOperand::Observation(
                        SharedMachineIntegerTerm::from_shared(ty, root).unwrap(),
                    )
                }),
            };
            let condition = read.integer_condition();
            let empty = PureFactContext::new();
            let exports = KernelTermExport::machine_export_count();
            for value in [false, true] {
                let fact = Proposition::condition_is(condition.clone(), value);
                assert!(!empty.contains_known(&fact));
                let held = empty.clone().assume_proposition(fact.clone());
                assert!(held.contains_known(&fact));
                assert!(
                    !held.contains_known(&Proposition::condition_is(condition.clone(), !value))
                );
                assert!(!empty.contains_known(&fact));
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    fn observe(ty: MachineIntegerType, variable: u64) -> SharedIntegerTerm {
        IntegerTerm::from_machine(ty, MachineTerm::Variable(Variable(variable)))
            .expect("a machine variable has an exact observation")
            .into()
    }

    fn constant(value: i64) -> SharedIntegerTerm {
        IntegerTerm::Constant(BigInt::from(value)).into()
    }

    #[test]
    fn compound_numeric_comparison_views_match_their_sources() {
        let _session = crate::kernel::VerificationSession::enter();
        let make = |n: i64| {
            Proposition::Or(
                Box::new(Proposition::condition_is(
                    ConditionTerm::IntegerNotEqual(
                        observe(MachineIntegerType::Int32, 850),
                        IntegerTerm::Subtract(constant(n), constant(n + 2147483648)).into(),
                    ),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(851)),
                        MachineTerm::constant(u32::MAX),
                    ),
                    false,
                )),
            )
        };
        let first = make(0);
        let second = make(1);
        let view = Proposition::Or(
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(850)),
                    MachineTerm::constant(i32::MIN as u32),
                ),
                false,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(851)),
                    MachineTerm::constant(u32::MAX),
                ),
                false,
            )),
        );
        assert_ne!(first, view);
        let mut context = PureFactContext::new();
        context.insert_proposition_fact(first.clone());
        context.insert_proposition_fact(second.clone());
        assert!(context.contains_proposition_fact(&view));
        assert!(context.prop_facts.contains(&first));
        assert!(!context.prop_facts.contains(&view));
    }

    #[test]
    fn native_facts_close_exact_integer_observation_queries_in_the_same_scope() {
        let comparisons: [fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm; 6] = [
            ConditionTerm::IntegerEqual,
            ConditionTerm::IntegerNotEqual,
            ConditionTerm::IntegerLessThan,
            ConditionTerm::IntegerLessEqual,
            ConditionTerm::IntegerGreaterThan,
            ConditionTerm::IntegerGreaterEqual,
        ];
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for comparison in comparisons {
                for truth in [false, true] {
                    let condition = comparison(observe(ty, 801), observe(ty, 803));
                    let goal = Proposition::condition_is(condition.clone(), truth);
                    let (native, native_truth) =
                        native_comparison_of_integer_observation(&condition, truth).unwrap();
                    let parent = PureFactContext::new();
                    let child = parent.clone().assume_condition(native, native_truth);
                    assert!(child.contains_known(&goal));
                    assert!(child.contains_known(&Proposition::Not(Box::new(
                        Proposition::condition_is(condition.clone(), !truth),
                    ))));
                    assert!(!child.contains_assumed_exact(&goal));
                    assert!(!parent.contains_known(&goal));
                    assert!(!child.contains_known(&Proposition::condition_is(condition, !truth)));
                    assert!(!child.contains_known(&Proposition::condition_is(
                        comparison(observe(ty, 802), observe(ty, 803)),
                        truth,
                    )));
                }
            }
        }
    }

    #[test]
    fn observation_sources_support_native_queries_without_duplicate_facts() {
        let comparisons: [fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm; 6] = [
            ConditionTerm::IntegerEqual,
            ConditionTerm::IntegerNotEqual,
            ConditionTerm::IntegerLessThan,
            ConditionTerm::IntegerLessEqual,
            ConditionTerm::IntegerGreaterThan,
            ConditionTerm::IntegerGreaterEqual,
        ];
        for ty in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for comparison in comparisons {
                for truth in [false, true] {
                    let condition = comparison(observe(ty, 1801), observe(ty, 1803));
                    let source = Proposition::condition_is(condition.clone(), truth);
                    let (native, value) =
                        native_comparison_of_integer_observation(&condition, truth).unwrap();
                    let goal = Proposition::condition_is(native.clone(), value);
                    let parent = PureFactContext::new();
                    let child = parent.clone().assume_proposition(source.clone());
                    assert!(child.contains_assumed_exact(&source));
                    assert!(!child.contains_assumed_exact(&goal));
                    assert!(child.contains_proposition_fact(&goal));
                    assert!(child.contains_known(&goal), "{ty:?} {condition:?} {truth}");
                    assert_eq!(child.decide(&native), Some(value));
                    assert!(child.contains_known(&Proposition::Not(Box::new(
                        Proposition::condition_is(native.clone(), !value)
                    ))));
                    assert!(!parent.contains_known(&goal));
                    assert!(!child.contains_known(&Proposition::condition_is(native, !value)));
                }
            }
        }
    }

    #[test]
    fn narrow_observation_orders_support_their_promoted_reading() {
        for ty in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
        ] {
            let source = ConditionTerm::IntegerLessThan(observe(ty, 1840), observe(ty, 1841));
            let (native, truth) = native_comparison_of_integer_observation(&source, true).unwrap();
            let promoted =
                crate::kernel::machine_integer::comparison::narrow_comparison_as_int32(&native)
                    .unwrap();
            let source = Proposition::condition_is(source, true);
            let facts = PureFactContext::new().assume_proposition(source);
            let goal = Proposition::condition_is(promoted.clone(), truth);
            assert!(facts.contains_known(&goal), "{ty:?}");
            assert_eq!(facts.decide(&promoted), Some(truth));
            assert!(!facts.contains_assumed_exact(&goal));
            assert!(!PureFactContext::new().contains_known(&goal));
        }
    }

    #[test]
    fn observation_contradictions_preserve_native_interoperability() {
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let source = ConditionTerm::IntegerEqual(observe(ty, 1850), observe(ty, 1851));
            let (native, truth) = native_comparison_of_integer_observation(&source, true).unwrap();
            let source = Proposition::condition_is(source, true);
            let native_only = PureFactContext::new().assume_condition(native, !truth);
            let facts = native_only.clone().assume_proposition(source);
            assert!(facts.is_inconsistent(), "{ty:?}");
            assert!(!native_only.is_inconsistent());
        }
        let bound = ConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::UInt64, 1852),
            uint64_max(),
        );
        assert!(
            PureFactContext::new()
                .assume_condition(bound, false)
                .is_inconsistent()
        );
    }

    #[test]
    fn observation_order_conflicts_keep_additive_rearrangement() {
        let ty = MachineIntegerType::Int32;
        let add = |a, b| MachineTerm::Binary {
            format: ty,
            op: crate::kernel::MachineBinaryOp::Add,
            left: Box::new(a),
            right: Box::new(b),
        };
        let left = add(add(word(1860), word(1861)), word(1862));
        let rearranged = add(word(1861), add(word(1862), word(1860)));
        let source = Proposition::condition_is(
            ConditionTerm::IntegerLessEqual(
                IntegerTerm::from_machine(ty, left).unwrap().into(),
                observe(ty, 1863),
            ),
            true,
        );
        let order = PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_than(word(1863), rearranged),
            true,
        );
        let facts = order.clone().assume_proposition(source);
        assert!(facts.is_inconsistent());
        assert!(!order.is_inconsistent());
    }

    #[test]
    fn observation_exclusion_at_signed_minimum_proves_negation_defined() {
        let x = word(1879);
        let source = Proposition::condition_is(
            ConditionTerm::IntegerNotEqual(
                observe(MachineIntegerType::Int32, 1879),
                IntegerTerm::Subtract(constant(-2147483647), constant(1)).into(),
            ),
            true,
        );
        let facts = PureFactContext::new().assume_proposition(source.clone());
        assert_eq!(
            facts.signed_interval_past_exclusions(&x),
            Some((-2147483647, 2147483647))
        );
        let overflow = ConditionTerm::signed_subtract_overflows(MachineTerm::constant(0), x);
        assert_eq!(facts.decide(&overflow), Some(false));
        for bound in crate::kernel::machine_integer::definedness::integer_bounds_of_definedness(
            &Proposition::condition_is(overflow, false),
        ) {
            let Proposition::ConditionIs(condition, truth) = bound else {
                unreachable!()
            };
            assert_eq!(facts.decide((&condition).native_compat()), Some(truth));
        }
        assert_eq!(
            PureFactContext::new().signed_interval_past_exclusions(&word(1879)),
            Some((i64::from(i32::MIN), i64::from(i32::MAX)))
        );
    }

    #[test]
    fn observation_equalities_preserve_additive_cancellation() {
        let ty = MachineIntegerType::Int32;
        let sum = |variable| {
            IntegerTerm::from_machine(ty, MachineTerm::add(word(variable), word(1872)))
                .unwrap()
                .into()
        };
        let source =
            Proposition::condition_is(ConditionTerm::IntegerEqual(sum(1870), sum(1871)), true);
        let facts = PureFactContext::new().assume_proposition(source);
        let goal = Proposition::condition_is(ConditionTerm::equal(word(1870), word(1871)), true);
        assert!(facts.contains_known(&goal));
        assert!(!PureFactContext::new().contains_known(&goal));
    }

    #[test]
    fn cancelled_observation_equalities_keep_original_order_endpoints() {
        let ty = MachineIntegerType::Int32;
        let left = MachineTerm::add(word(1890), word(1892));
        let right = MachineTerm::add(word(1891), word(1892));
        let equality = ConditionTerm::IntegerEqual(
            IntegerTerm::from_machine(ty, left.clone()).unwrap().into(),
            IntegerTerm::from_machine(ty, right.clone()).unwrap().into(),
        );
        let order = ConditionTerm::signed_less_than(left, right);
        let mut index = contradictions::ContextContradictions::default();
        index.adjust(&order, true);
        index.adjust(&equality, true);
        assert!(index.index(Vec::new).is_contradictory());
        let source = Proposition::condition_is(equality, true);
        let ordered = PureFactContext::new().assume_condition(order, true);
        let facts = ordered.clone().assume_proposition(source);
        assert!(facts.is_inconsistent());
        assert!(!ordered.is_inconsistent());
    }

    #[test]
    fn cancelled_observation_disequalities_keep_the_original_source() {
        let ty = MachineIntegerType::Int32;
        let observe_sum = |a, b| {
            IntegerTerm::from_machine(ty, MachineTerm::add(a, b))
                .unwrap()
                .into()
        };
        let source = Proposition::condition_is(
            ConditionTerm::IntegerNotEqual(
                observe_sum(word(1880), word(1882)),
                observe_sum(word(1881), word(1882)),
            ),
            true,
        );
        let facts = PureFactContext::new().assume_proposition(source);
        let goal = Proposition::condition_is(ConditionTerm::equal(word(1880), word(1881)), false);
        assert!(facts.contains_known(&goal));
        assert!(!facts.contains_assumed_exact(&goal));
        assert!(!PureFactContext::new().contains_known(&goal));
        let impossible = Proposition::condition_is(
            ConditionTerm::IntegerNotEqual(
                observe_sum(word(1880), word(1881)),
                observe_sum(word(1881), word(1880)),
            ),
            true,
        );
        let facts = PureFactContext::new().assume_proposition(impossible);
        assert!(facts.is_inconsistent());
    }

    #[test]
    fn shared_bound_premise_selects_written_source() {
        use crate::kernel::machine_integer::comparison::condition_for_operand_views;
        use crate::kernel::{KernelTermImport, MachineOperandView};
        let _session = crate::kernel::VerificationSession::enter();
        let term = MachineTerm::sign_cast32(
            MachineIntegerType::UInt32,
            MachineIntegerType::Int32,
            MachineTerm::add(word(189131), word(189132)),
        );
        let zero = MachineTerm::constant(0);
        let native = ConditionTerm::signed_less_equal(zero.clone(), term.clone());
        let source = Proposition::condition_is(native, true);
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &term)
            .unwrap();
        let goal = condition_for_operand_views(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            [
                MachineOperandView::Legacy(&zero),
                MachineOperandView::Shared(&root),
            ],
        );
        let parent = PureFactContext::new();
        let child = parent.clone().assume_proposition(source.clone());
        let select = |context: &PureFactContext| {
            context
                .checked_order_bounds
                .exact_observation_source(&goal, true)
        };
        assert_eq!(select(&child), Some(source.clone()));
        assert_eq!(select(&parent), None);
        assert_eq!(select(&child), Some(source.clone()));
        for _ in 0..2 {
            let (_, used) = collect_consulted_premises(|| {
                record_consulted_premises(&child, &Proposition::condition_is(goal.clone(), true));
            });
            assert_eq!(used, vec![source.clone()]);
        }
    }

    #[test]
    fn observation_aliases_retain_each_supporting_source() {
        let x = observe(MachineIntegerType::UInt32, 1810);
        let first = Proposition::condition_is(
            ConditionTerm::IntegerLessEqual(x.clone(), constant(100)),
            true,
        );
        let second =
            Proposition::condition_is(ConditionTerm::IntegerGreaterEqual(constant(100), x), true);
        let goal = Proposition::condition_is(
            ConditionTerm::unsigned_less_equal(word(1810), MachineTerm::constant(100)),
            true,
        );
        for source in [first, second] {
            let facts = PureFactContext::new().assume_proposition(source);
            assert!(facts.contains_known(&goal));
        }
    }

    #[test]
    fn signed_bound_selection_preserves_sources_and_polarity() {
        for (ty, width) in [
            (MachineIntegerType::Int32, SignedDefinedWidth::Int32),
            (MachineIntegerType::Int64, SignedDefinedWidth::Int64),
        ] {
            let first = Proposition::condition_is(
                ConditionTerm::IntegerGreaterThan(observe(ty, 1815), constant(100)),
                false,
            );
            let second = Proposition::condition_is(
                ConditionTerm::IntegerGreaterEqual(constant(100), observe(ty, 1815)),
                true,
            );
            let parent = PureFactContext::new().assume_proposition(first.clone());
            let child = parent.clone().assume_proposition(second.clone());
            let selected = child.signed_constant_bound_facts(width, &word(1815));
            assert_eq!(selected.len(), 1);
            assert!(selected[0] == first || selected[0] == second);
            let second_only = PureFactContext::new().assume_proposition(second.clone());
            assert_eq!(
                second_only.signed_constant_bound_facts(width, &word(1815)),
                vec![second]
            );
            assert_eq!(
                parent.signed_constant_bound_facts(width, &word(1815)),
                vec![first]
            );
        }
    }

    #[test]
    fn observation_equalities_join_native_classes_and_transport_orders() {
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let original = ConditionTerm::IntegerEqual(observe(ty, 1820), observe(ty, 1821));
            let native = |left, right| {
                native_comparison_of_integer_observation(
                    &ConditionTerm::IntegerEqual(observe(ty, left), observe(ty, right)),
                    true,
                )
                .unwrap()
                .0
            };
            let source = Proposition::condition_is(original, true);
            let weakened = PureFactContext::new()
                .assume_condition(native(1821, 1822), true)
                .assume_condition(
                    ConditionTerm::IntegerLessThan(observe(ty, 1820), observe(ty, 1823)),
                    true,
                );
            let facts = weakened.clone().assume_proposition(source);
            let goal = Proposition::condition_is(native(1820, 1822), true);
            assert!(facts.contains_known(&goal), "{ty:?}");
            let order = native_comparison_of_integer_observation(
                &ConditionTerm::IntegerLessThan(observe(ty, 1822), observe(ty, 1823)),
                true,
            )
            .unwrap()
            .0;
            assert!(
                facts.contains_known(&Proposition::condition_is(order.clone(), true)),
                "{ty:?}"
            );
            assert!(!weakened.contains_known(&goal));
            assert!(!weakened.contains_known(&Proposition::condition_is(order, true)));
        }
    }

    #[test]
    fn a_definedness_bound_over_a_promoted_byte_reads_back_to_its_fact() {
        // `total + (int32)byte`: the byte's `int32` observation is the
        // byte's own, and the bound still names the `int32` overflow fact.
        // The byte is a C narrowing, a value of 8 bits; its promotion is a
        // widening node of its own (rule K8, a relation), which the
        // overflow test reads.
        let byte = MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: Box::new(MachineTerm::Variable(Variable(821))),
            from: MachineIntegerType::Int32,
            to: MachineIntegerType::UInt8,
        };
        let promoted = MachineTerm::machine_integer_cast(
            MachineIntegerType::UInt8,
            MachineIntegerType::Int32,
            byte.clone(),
        );
        let condition = ConditionTerm::machine_overflows(
            MachineIntegerType::Int32,
            OverflowOperation::Add,
            MachineTerm::Variable(Variable(822)),
            promoted.clone(),
        );
        assert!(
            matches!(&condition, ConditionTerm::Overflows { right, .. } if **right == promoted)
        );
        let fact = Proposition::condition_is(condition, false);
        let bounds = integer_bounds_of_definedness(&fact);
        assert_eq!(bounds.len(), 2);
        for bound in &bounds {
            assert_eq!(definedness_of_integer_bound(bound).as_ref(), Some(&fact));
        }
    }

    #[test]
    fn a_narrow_observation_is_native_only_for_an_extended_word() {
        // A conversion into 8 bits is a native 8-bit value, so its
        // observation compares as a native 8-bit comparison and reads back
        // exactly.
        let byte = MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: Box::new(MachineTerm::Variable(Variable(811))),
            from: MachineIntegerType::Int32,
            to: MachineIntegerType::UInt8,
        };
        let observed: SharedIntegerTerm =
            IntegerTerm::from_machine(MachineIntegerType::UInt8, byte.clone())
                .unwrap()
                .into();
        let condition = ConditionTerm::IntegerLessThan(observed, constant(255));
        let (native, truth) = native_comparison_of_integer_observation(&condition, true).unwrap();
        assert_eq!(
            native,
            ConditionTerm::narrow_compare(
                MachineIntegerType::UInt8,
                CompareRelation::LessThan,
                byte,
                MachineTerm::narrow_constant(MachineIntegerType::UInt8, 255)
            )
        );
        assert_eq!(
            integer_observations_of_native_comparison(&Proposition::condition_is(native, truth)),
            vec![Proposition::condition_is(condition, true)]
        );
        // An arbitrary word's byte is not the word: 256 is not below 255,
        // but its byte, 0, is.
        let sum = IntegerTerm::from_machine(
            MachineIntegerType::UInt8,
            binary_node!(
                Int32,
                Add,
                Box::new(MachineTerm::Variable(Variable(812))),
                Box::new(MachineTerm::constant(1)),
            ),
        )
        .unwrap();
        let condition = ConditionTerm::IntegerLessThan(sum.into(), constant(255));
        assert!(native_comparison_of_integer_observation(&condition, true).is_none());
    }

    fn uint32_difference_from(value: i64, variable: u64) -> SharedIntegerTerm {
        IntegerTerm::Subtract(
            constant(value),
            observe(MachineIntegerType::UInt32, variable),
        )
        .into()
    }

    fn uint32_guard(value: u32, left: u64, right: u64) -> ConditionTerm {
        ConditionTerm::unsigned_less_equal(
            word(left),
            MachineTerm::subtract(MachineTerm::constant(value), word(right)),
        )
    }

    fn uint64_max() -> SharedIntegerTerm {
        IntegerTerm::Constant(BigInt::from(u64::MAX)).into()
    }

    /// `forall (k: uint64) { antecedent implies word(832) == 0 }`.
    fn quantified_over_k(antecedent: Proposition) -> Proposition {
        Proposition::ForAll {
            var: Variable(830),
            sort: Sort::ProgramInteger(MachineIntegerType::UInt64),
            body: Box::new(Proposition::Implies(
                Box::new(antecedent),
                Box::new(Proposition::condition_is(
                    ConditionTerm::equal(word(832), MachineTerm::constant(0)),
                    true,
                )),
            )),
            name: BinderName::written("k"),
        }
    }

    #[test]
    fn a_quantified_integer_antecedent_through_an_in_range_sum_files_its_native_reading() {
        // forall k { to_integer(k) < to_integer(len) + 1 implies ... } is
        // forall k { k < len + 1u64 implies ... } once len + 1 cannot wrap.
        let sum: SharedIntegerTerm =
            IntegerTerm::Add(observe(MachineIntegerType::UInt64, 831), constant(1)).into();
        let reading =
            ConditionTerm::IntegerLessThan(observe(MachineIntegerType::UInt64, 830), sum.clone());
        let (native, truth, _) = native_comparison_through_integer_operations(&reading, true)
            .expect("the sum has a native reading");
        let integer_fact = quantified_over_k(Proposition::condition_is(reading, true));
        let native_fact = quantified_over_k(Proposition::condition_is(native, truth));
        let unbounded = PureFactContext::new().assume_proposition(integer_fact.clone());
        assert!(!unbounded.contains_known(&native_fact));
        let bounded = PureFactContext::new()
            .assume_condition(ConditionTerm::IntegerLessEqual(sum, uint64_max()), true)
            .assume_proposition(integer_fact);
        assert!(bounded.contains_known(&native_fact));
    }

    #[test]
    fn a_quantified_antecedent_bound_that_names_the_binder_files_nothing() {
        // to_integer(k) + 1 <= to_integer(len) needs a bound on k + 1, which
        // differs for each k, so no fact about the context supplies it.
        let sum: SharedIntegerTerm =
            IntegerTerm::Add(observe(MachineIntegerType::UInt64, 830), constant(1)).into();
        let reading =
            ConditionTerm::IntegerLessEqual(sum.clone(), observe(MachineIntegerType::UInt64, 831));
        let (native, truth, _) = native_comparison_through_integer_operations(&reading, true)
            .expect("the sum has a native reading");
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::IntegerLessEqual(sum, uint64_max()), true)
            .assume_proposition(quantified_over_k(Proposition::condition_is(reading, true)));
        assert!(
            !context.contains_known(&quantified_over_k(Proposition::condition_is(native, truth)))
        );
    }

    #[test]
    fn an_integer_bound_through_an_in_range_difference_files_the_native_guard() {
        // to_integer(a) <= 4294967295 - to_integer(b) is a <= 4294967295u32 - b:
        // the difference cannot wrap, so no bound is needed.
        let reading = ConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::UInt32, 1),
            uint32_difference_from(4_294_967_295, 2),
        );
        let (_, _, bounds) = native_comparison_through_integer_operations(&reading, true).unwrap();
        assert!(bounds.is_empty());
        let context = PureFactContext::new().assume_condition(reading, true);
        assert_eq!(context.decide(&uint32_guard(u32::MAX, 1, 2)), Some(true));
    }

    #[test]
    fn a_difference_that_may_wrap_files_the_native_guard_only_with_its_bound() {
        // 4294967294 - to_integer(b) is below zero for b == 4294967295.
        let reading = ConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::UInt32, 1),
            uint32_difference_from(4_294_967_294, 2),
        );
        let (_, _, bounds) = native_comparison_through_integer_operations(&reading, true).unwrap();
        assert_eq!(bounds.len(), 1);
        assert!(bounds[0].lower);
        let unbounded = PureFactContext::new().assume_condition(reading.clone(), true);
        assert_ne!(
            unbounded.decide(&uint32_guard(u32::MAX - 1, 1, 2)),
            Some(true)
        );
        // The bound itself, in either spelling, then supplies the reading.
        for bound in [
            ConditionTerm::IntegerGreaterEqual(
                uint32_difference_from(4_294_967_294, 2),
                constant(0),
            ),
            ConditionTerm::IntegerLessEqual(constant(0), uint32_difference_from(4_294_967_294, 2)),
        ] {
            let bounded = PureFactContext::new()
                .assume_condition(bound, true)
                .assume_condition(reading.clone(), true);
            assert_eq!(
                bounded.decide(&uint32_guard(u32::MAX - 1, 1, 2)),
                Some(true)
            );
        }
        // A guard with a different constant is not this reading.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerLessEqual(
                observe(MachineIntegerType::UInt32, 1),
                uint32_difference_from(4_294_967_295, 2),
            ),
            true,
        );
        assert_ne!(
            context.decide(&uint32_guard(u32::MAX - 1, 1, 2)),
            Some(true)
        );
    }

    #[test]
    fn a_sum_side_needs_its_upper_bound() {
        // to_integer(a) + to_integer(b) <= to_integer(c) reads as the native
        // a + b <= c only once the sum stays in uint32.
        let sum = || -> SharedIntegerTerm {
            IntegerTerm::Add(
                observe(MachineIntegerType::UInt32, 1),
                observe(MachineIntegerType::UInt32, 2),
            )
            .into()
        };
        let reading =
            ConditionTerm::IntegerLessEqual(sum(), observe(MachineIntegerType::UInt32, 3));
        let native =
            ConditionTerm::unsigned_less_equal(MachineTerm::add(word(1), word(2)), word(3));
        let unbounded = PureFactContext::new().assume_condition(reading.clone(), true);
        assert_ne!(unbounded.decide(&native), Some(true));
        let bounded = PureFactContext::new()
            .assume_condition(
                ConditionTerm::IntegerLessEqual(sum(), constant(4_294_967_295)),
                true,
            )
            .assume_condition(reading, true);
        assert_eq!(bounded.decide(&native), Some(true));
    }

    #[test]
    fn both_integer_bounds_of_a_signed_difference_file_its_definedness() {
        let overflow = ConditionTerm::signed_subtract_overflows(word(1), word(2));
        let upper = ConditionTerm::IntegerLessEqual(difference(1, 2), constant(2_147_483_647));
        let lowers = [
            ConditionTerm::IntegerGreaterEqual(difference(1, 2), constant(-2_147_483_648)),
            ConditionTerm::IntegerLessEqual(constant(-2_147_483_648), difference(1, 2)),
        ];
        let one = PureFactContext::new().assume_condition(upper.clone(), true);
        assert_ne!(one.decide(&overflow), Some(false));
        for lower in lowers {
            let one = PureFactContext::new().assume_condition(lower.clone(), true);
            assert_ne!(one.decide(&overflow), Some(false));
            for (first, second) in [(&upper, &lower), (&lower, &upper)] {
                let both = PureFactContext::new()
                    .assume_condition(first.clone(), true)
                    .assume_condition(second.clone(), true);
                assert_eq!(both.decide(&overflow), Some(false));
            }
        }
        // A bound one past the range is not the definedness bound.
        let wide = PureFactContext::new()
            .assume_condition(
                ConditionTerm::IntegerLessEqual(difference(1, 2), constant(2_147_483_648)),
                true,
            )
            .assume_condition(
                ConditionTerm::IntegerGreaterEqual(difference(1, 2), constant(-2_147_483_648)),
                true,
            );
        assert_ne!(wide.decide(&overflow), Some(false));
    }

    mod scaling_tests {
        use super::*;
        include!("../scaling_tests/kernel/assumptions/integer_observation_tests.rs");
    }

    fn word(variable: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(variable))
    }

    fn difference(left: u64, right: u64) -> SharedIntegerTerm {
        IntegerTerm::Subtract(
            observe(MachineIntegerType::Int32, left),
            observe(MachineIntegerType::Int32, right),
        )
        .into()
    }

    #[test]
    fn an_integer_equality_files_its_wrapped_word_equality() {
        // to_integer(a) - to_integer(b) == 0 implies the word a - b is 0.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerEqual(difference(1, 2), constant(0)),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::equal(
                MachineTerm::subtract(word(1), word(2)),
                MachineTerm::constant(0)
            )),
            Some(true)
        );
    }

    #[test]
    fn a_wrapped_word_equality_does_not_decide_its_integer_equality() {
        // The word a - b can be 0 when the Integer difference is 2^32.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::equal(
                MachineTerm::subtract(word(1), word(2)),
                MachineTerm::constant(0),
            ),
            true,
        );
        assert_ne!(
            context.decide(&ConditionTerm::IntegerEqual(difference(1, 2), constant(0))),
            Some(true)
        );
    }

    #[test]
    fn an_integer_order_over_arithmetic_files_no_word_fact() {
        let order = ConditionTerm::IntegerLessEqual(difference(1, 2), constant(0));
        assert_eq!(wrapped_equality_of_integer_equality(&order, true), None);
        let equality = ConditionTerm::IntegerEqual(difference(1, 2), constant(0));
        assert_eq!(wrapped_equality_of_integer_equality(&equality, false), None);
    }

    #[test]
    fn an_integer_bound_files_its_native_comparison() {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerLessEqual(constant(0), observe(MachineIntegerType::Int32, 1)),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::signed_less_equal(
                MachineTerm::constant(0),
                word(1)
            )),
            Some(true)
        );
    }

    #[test]
    fn an_unsigned_bound_files_the_unsigned_comparison() {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerLessThan(observe(MachineIntegerType::UInt32, 1), constant(10)),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::unsigned_less_than(
                word(1),
                MachineTerm::constant(10)
            )),
            Some(true)
        );
    }

    #[test]
    fn a_false_comparison_files_its_negation() {
        // not (to_integer(x) < 5) is 5 <= x.
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerLessThan(observe(MachineIntegerType::Int32, 1), constant(5)),
            false,
        );
        assert_eq!(
            context.decide(&ConditionTerm::signed_less_equal(
                MachineTerm::constant(5),
                word(1)
            )),
            Some(true)
        );
    }

    #[test]
    fn an_integer_disequality_files_a_false_native_equality() {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::IntegerNotEqual(
                observe(MachineIntegerType::Int32, 1),
                observe(MachineIntegerType::Int32, 2),
            ),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::equal(word(1), word(2))),
            Some(false)
        );
    }

    #[test]
    fn a_native_comparison_reads_back_as_its_integer_observation() {
        for (condition, truth) in [
            (
                ConditionTerm::IntegerLessEqual(
                    constant(1),
                    observe(MachineIntegerType::UInt32, 1),
                ),
                true,
            ),
            (
                ConditionTerm::IntegerLessThan(
                    observe(MachineIntegerType::Int32, 1),
                    observe(MachineIntegerType::Int32, 2),
                ),
                true,
            ),
            (
                ConditionTerm::IntegerLessEqual(
                    observe(MachineIntegerType::UInt64, 1),
                    constant(7),
                ),
                true,
            ),
            (
                ConditionTerm::IntegerEqual(observe(MachineIntegerType::Int64, 1), constant(-3)),
                false,
            ),
        ] {
            let (native, native_truth) =
                native_comparison_of_integer_observation(&condition, truth).unwrap();
            let fact = Proposition::condition_is(native.clone(), native_truth);
            let lifted = integer_observations_of_native_comparison(&fact);
            assert!(!lifted.is_empty(), "{condition:?}");
            for reading in lifted {
                let Proposition::ConditionIs(reading, reading_truth) = reading else {
                    unreachable!()
                };
                // Each reading files exactly the native fact it came from.
                assert_eq!(
                    native_comparison_of_integer_observation(
                        (&reading).native_compat(),
                        reading_truth
                    ),
                    Some((native.clone(), native_truth))
                );
            }
        }
        // A native order the forward map spells the other way round, as
        // `x >= 1` is stated beside `1 <= x`, reads back as the same bound.
        let mirrored = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(word(1)),
                right: Box::new(MachineTerm::constant(1)),
            },
            true,
        );
        assert!(
            integer_observations_of_native_comparison(&mirrored).contains(
                &Proposition::condition_is(
                    ConditionTerm::IntegerLessEqual(
                        constant(1),
                        observe(MachineIntegerType::Int32, 1)
                    ),
                    true,
                )
            )
        );
        // The same holds in the 64-bit unsigned family, at either polarity:
        // `x >= 32u64` and a false `0u64 < x` read as their bounds.
        for (fact, reading) in [
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::GreaterEqual,
                    left: Box::new(word(1)),
                    right: Box::new(MachineTerm::uint64_constant(32)),
                },
                ConditionTerm::IntegerLessEqual(
                    constant(32),
                    observe(MachineIntegerType::UInt64, 1),
                ),
            ),
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::LessThan,
                    left: Box::new(MachineTerm::uint64_constant(0)),
                    right: Box::new(word(1)),
                },
                ConditionTerm::IntegerLessEqual(
                    observe(MachineIntegerType::UInt64, 1),
                    constant(0),
                ),
            ),
        ] {
            let truth = matches!(
                fact,
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::GreaterEqual,
                    ..
                }
            );
            assert_eq!(
                integer_observations_of_native_comparison(&Proposition::condition_is(fact, truth)),
                vec![Proposition::condition_is(reading, true)]
            );
        }
        // Facts other than native comparisons read as nothing.
        assert!(
            integer_observations_of_native_comparison(&Proposition::condition_is(
                ConditionTerm::IntegerLessEqual(constant(1), observe(MachineIntegerType::Int32, 1)),
                true,
            ))
            .is_empty()
        );
    }

    #[test]
    fn shared_comparison_queries_read_native_sources_in_both_polarities() {
        use crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison;
        for ty in [
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
                CompareRelation::LessThan,
                CompareRelation::LessEqual,
                CompareRelation::GreaterThan,
                CompareRelation::GreaterEqual,
            ] {
                for truth in [false, true] {
                    let _session = crate::kernel::VerificationSession::enter();
                    let source =
                        ConditionTerm::machine_compare(ty, relation, word(994301), word(994302));
                    let source = Proposition::condition_is(source, truth);
                    let readings = integer_observations_of_native_comparison(&source);
                    assert!(!readings.is_empty(), "{ty:?} {relation:?}");
                    let parent = PureFactContext::new();
                    let child = parent.clone().assume_proposition(source);
                    for reading in readings {
                        let Proposition::ConditionIs(query, value) = reading else {
                            unreachable!()
                        };
                        assert_eq!(
                            parent.decide((&query).native_compat()),
                            None,
                            "{ty:?} {relation:?}"
                        );
                        assert!(
                            child
                                .equality_graph
                                .knows_condition((&query).native_compat(), value),
                            "{ty:?} {relation:?} {truth}"
                        );
                        assert!(
                            !child
                                .equality_graph
                                .knows_condition((&query).native_compat(), !value),
                            "{ty:?} {relation:?} {truth}"
                        );
                        assert_eq!(
                            child.decide((&query).native_compat()),
                            Some(value),
                            "{ty:?} {relation:?} {truth}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn observation_dispatch_preserves_native_arithmetic_order_rules() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = word(994501);
        let y = word(994502);
        let upper = MachineTerm::constant(i32::MAX as u32);
        let context = PureFactContext::new()
            .assume_condition(ConditionTerm::signed_less_than(x.clone(), upper), true)
            .assume_condition(
                ConditionTerm::signed_greater_equal(x.clone(), MachineTerm::constant(0)),
                true,
            );
        let plus_one = MachineTerm::add(x.clone(), MachineTerm::constant(1));
        let cases = [
            ConditionTerm::signed_less_than(x.clone(), plus_one.clone()),
            ConditionTerm::signed_less_equal(x.clone(), plus_one),
        ];
        for native in cases {
            let expected = context.decide(&native);
            assert_eq!(expected, Some(true));
            for reading in
                integer_observations_of_native_comparison(&Proposition::condition_is(native, true))
            {
                let Proposition::ConditionIs(query, value) = reading else {
                    unreachable!()
                };
                assert_eq!(
                    context.decide((&query).native_compat()),
                    Some(value),
                    "{query:?}"
                );
            }
        }
        let constants = PureFactContext::new()
            .assume_condition(
                ConditionTerm::equal(x.clone(), MachineTerm::constant(1)),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(y.clone(), MachineTerm::constant(2)),
                true,
            );
        let native =
            ConditionTerm::signed_less_than(MachineTerm::add(x, y), MachineTerm::constant(4));
        assert_eq!(constants.decide(&native), Some(true));
        for reading in
            integer_observations_of_native_comparison(&Proposition::condition_is(native, true))
        {
            let Proposition::ConditionIs(query, value) = reading else {
                unreachable!()
            };
            assert_eq!(
                constants.decide((&query).native_compat()),
                Some(value),
                "{query:?}"
            );
        }
    }

    #[test]
    fn a_native_fact_decides_its_integer_observation() {
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_equal(word(1), MachineTerm::constant(3)),
            true,
        );
        assert_eq!(
            context.decide(&ConditionTerm::IntegerLessEqual(
                observe(MachineIntegerType::Int32, 1),
                constant(3)
            )),
            Some(true)
        );
        assert_eq!(
            context.decide(&ConditionTerm::IntegerGreaterThan(
                observe(MachineIntegerType::Int32, 1),
                constant(3)
            )),
            Some(false)
        );
    }

    #[test]
    fn an_out_of_range_constant_files_nothing() {
        let condition = ConditionTerm::IntegerLessThan(
            observe(MachineIntegerType::Int32, 1),
            constant(i64::from(i32::MAX) + 1),
        );
        assert_eq!(
            native_comparison_of_integer_observation(&condition, true),
            None
        );
    }

    #[test]
    fn observations_of_different_types_file_nothing() {
        let condition = ConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::Int32, 1),
            observe(MachineIntegerType::UInt32, 2),
        );
        assert_eq!(
            native_comparison_of_integer_observation(&condition, true),
            None
        );
    }
}

/// An upper bound on the execution-range variables a context's facts
/// mention, kept as facts are filed without reading a state's contents.
/// Filing a fact takes the ceiling of its written syntax into `base`; a fact
/// that names a state is also queued in `pending`. The first execution
/// that asks takes each queued fact's whole ceiling, states included,
/// and caches the result for this context version; the next fact filed
/// rebases on that result, so each queued fact is taken whole once along a
/// path. Forks share `pending` and the cache until one of them files a fact.
#[derive(Clone, Default)]
pub(super) struct ExecutionVariableCeiling {
    base: Option<Variable>,
    pending: crate::kernel::proof::PersistentSequence<ExecutionVariableCeilingFact>,
    cached: std::sync::Arc<std::sync::OnceLock<Option<Variable>>>,
}

#[derive(Clone)]
pub(super) enum ExecutionVariableCeilingFact {
    Condition(ConditionTerm),
    Proposition(Proposition),
}

impl std::fmt::Debug for ExecutionVariableCeiling {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ExecutionVariableCeiling")
            .field("base", &self.base)
            .field("pending", &self.pending.len())
            .finish()
    }
}

impl ExecutionVariableCeiling {
    fn file_condition(&mut self, condition: &ConditionTerm) {
        let (syntax, names_program_point) =
            crate::kernel::reasoning::variable_collection::condition_syntax_execution_variable_ceiling(
                condition,
            );
        self.file(
            syntax,
            names_program_point.then(|| ExecutionVariableCeilingFact::Condition(condition.clone())),
        );
    }

    fn file_proposition(&mut self, proposition: &Proposition) {
        let (syntax, names_program_point) =
            crate::kernel::reasoning::variable_collection::proposition_syntax_execution_variable_ceiling(
                proposition,
            );
        self.file(
            syntax,
            names_program_point
                .then(|| ExecutionVariableCeilingFact::Proposition(proposition.clone())),
        );
    }

    fn file(&mut self, syntax: Option<Variable>, deferred: Option<ExecutionVariableCeilingFact>) {
        if let Some(ceiling) = self.cached.get() {
            self.base = self.base.max(*ceiling);
            self.pending = Default::default();
        }
        self.base = self.base.max(syntax);
        if let Some(fact) = deferred {
            self.pending.push(fact);
        }
        self.cached = std::sync::Arc::new(std::sync::OnceLock::new());
    }

    fn get(&self) -> Option<Variable> {
        use crate::kernel::reasoning::variable_collection::{
            condition_execution_variable_ceiling, proposition_execution_variable_ceiling,
        };
        *self.cached.get_or_init(|| {
            self.pending
                .iter()
                .map(|fact| {
                    #[cfg(test)]
                    WHOLE_CEILING_FACTS.with(|count| count.set(count.get() + 1));
                    match fact {
                        ExecutionVariableCeilingFact::Condition(condition) => {
                            condition_execution_variable_ceiling(condition)
                        }
                        ExecutionVariableCeilingFact::Proposition(proposition) => {
                            proposition_execution_variable_ceiling(proposition)
                        }
                    }
                })
                .fold(self.base, Option::max)
        })
    }
}

#[cfg(test)]
mod execution_variable_ceiling_tests {
    use super::*;

    fn word(offset: i64) -> Address {
        Address {
            base: AddressBase::Concrete("a".into()),
            offset: AddressOffset::Constant(offset),
        }
    }

    fn execution_variable(offset: u64) -> Variable {
        Variable(ExecutionBudget::KERNEL_VARIABLE_BASE + offset)
    }

    /// A fact naming a state whose stored value holds `variable`, though
    /// the fact's own syntax names no variable.
    fn fact_over_state_holding(variable: Variable) -> ConditionTerm {
        let memory = SymbolicMemory::new().with_block("a", 8).store(
            word(0),
            ProgramValue::Int32(MachineTerm::Variable(variable)),
        );
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::MemoryLoad(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
                Box::new(word(4)),
                crate::kernel::LoadKind::Int32,
            )),
            right: Box::new(MachineTerm::constant(0)),
        }
    }

    #[test]
    fn the_ceiling_covers_variables_only_a_named_state_holds() {
        let context = PureFactContext::new();
        assert_eq!(context.execution_variable_ceiling(), None);
        let context = context
            .assume_condition(fact_over_state_holding(execution_variable(7)), true)
            .assume_proposition(Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(MachineTerm::Variable(execution_variable(3))),
                    right: Box::new(MachineTerm::constant(1)),
                },
                true,
            ));
        assert!(context.execution_variable_ceiling() >= Some(execution_variable(7)));
    }

    #[test]
    fn shared_ceiling_keeps_live_load_dependencies_and_execution_id_limits() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory =
            crate::kernel::intern_memory_ref(&SymbolicMemory::new().with_block("a", 8).store(
                word(0),
                ProgramValue::Int32(MachineTerm::Variable(execution_variable(71))),
            ));
        let load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &word(4),
            LoadKind::Int32,
            4,
        );
        let mut root = KernelTerm::variable(KernelType::Program(ProgramType::Int32), load);
        for variable in [execution_variable(3), Variable(7), Variable(u64::MAX)] {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Multiply,
                [
                    root,
                    KernelTerm::variable(KernelType::Program(ProgramType::Int32), variable),
                ],
            );
        }
        let observation =
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap();
        let condition = ConditionTerm::integer_less_equal(
            IntegerTerm::Machine(observation.clone()),
            IntegerTerm::constant_i64(7),
        );
        let exports = KernelTermExport::machine_export_count();
        let (syntax, deferred) = crate::kernel::reasoning::variable_collection::condition_syntax_execution_variable_ceiling(&condition);
        assert_eq!(syntax, Some(execution_variable(3)));
        assert!(deferred);
        let facts = PureFactContext::new().assume_condition(condition, true);
        assert_eq!(
            facts.execution_variable_ceiling(),
            Some(execution_variable(71))
        );
        assert!(!observation.has_boxed_operand());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    /// A composition fact's syntax ceiling is read from its context's cached
    /// canonical fact set: it agrees with walking every held fact, and the
    /// context one more fact derives computes only that insertion's path.
    #[test]
    fn composition_ceiling_reads_the_cached_fact_set() {
        let owned = |index: u64| {
            ResourceFact::own_memory(MemoryRange::new(
                Address::symbolic(execution_variable(index)),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))
        };
        use crate::kernel::reasoning::variable_collection::{
            COLLECTED_RESOURCE_FACTS, collect_proposition_bitvector_variables,
            execution_variable_ceiling, proposition_syntax_execution_variable_ceiling,
        };
        let walked = |proposition: &Proposition| {
            execution_variable_ceiling(Some(false), |variables| {
                collect_proposition_bitvector_variables(proposition, variables)
            })
        };
        for size in [16u64, 64, 256] {
            let resources = (0..size).fold(ResourceContext::new(), |resources, index| {
                resources.unchecked_with_fact(owned(index))
            });
            let composition = Proposition::ResourceComposition(resources.clone());
            let ceiling = proposition_syntax_execution_variable_ceiling(&composition);
            assert_eq!(ceiling, walked(&composition), "size {size}");
            assert_eq!(ceiling, (Some(execution_variable(size - 1)), false));
            let next = Proposition::ResourceComposition(resources.unchecked_with_fact(owned(size)));
            COLLECTED_RESOURCE_FACTS.with(|count| count.set(0));
            let ceiling = proposition_syntax_execution_variable_ceiling(&next);
            assert_eq!(ceiling, (Some(execution_variable(size)), false));
            // A treap path: logarithmic in the held facts, where walking
            // the composition visits all `size + 1` of them.
            let visits = COLLECTED_RESOURCE_FACTS.with(Cell::get);
            assert!(
                visits <= 4 * size.ilog2() as usize,
                "size {size}: {visits} facts visited"
            );
        }
    }

    #[test]
    fn asking_after_every_fact_takes_each_state_fact_whole_once() {
        for size in [8, 32] {
            WHOLE_CEILING_FACTS.with(|count| count.set(0));
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_condition(
                    fact_over_state_holding(execution_variable(index as u64)),
                    true,
                );
                assert_eq!(
                    context.execution_variable_ceiling(),
                    Some(execution_variable(index as u64))
                );
            }
            assert_eq!(WHOLE_CEILING_FACTS.with(Cell::get), size, "size {size}");
        }
    }
}

#[cfg(test)]
mod framed_opaque_pointer_entry_tests {
    use super::*;
    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/framed_opaque_pointer_entry_tests.rs");
    }
}

#[cfg(test)]
mod annotated_numeric_pointer_condition_tests {
    use super::*;

    #[test]
    fn address_conditions_ignore_annotations_without_equating_pointer_domains() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let p = Address::symbolic(Variable(995_100));
        let q = Address::symbolic(Variable(995_101));
        let address = |p: Address| {
            MachineTerm::object_pointer_address(p, Some(CAccessClass::Scalar(CScalarClass::Int)))
        };
        let source = ConditionTerm::uint64_equal(address(p.clone()), address(q.clone()));
        let target =
            crate::kernel::eval::program_pointer_comparison_condition(p.clone(), q.clone());
        for value in [false, true] {
            let context = PureFactContext::new().assume_condition(source.clone(), value);
            assert_eq!(context.fast_leaf_decision(&target, &[]), Some(value));
            assert!(!context.pointer_provenance_match(
                &Pointer::new(p.clone(), ProgramType::Int32Pointer),
                &Pointer::new(q.clone(), ProgramType::Int32Pointer)
            ));
            assert_eq!(
                PureFactContext::new().fast_leaf_decision(&target, &[]),
                None
            );
        }
    }
}

#[cfg(test)]
mod decided_algebraic_if_tests;

#[cfg(test)]
mod bool_sort_tests;

/// The order facts of a context, each filed as its own condition under the
/// lower end an order walk follows it from. The exact order walks
/// (`has_exact_order_path`, `exact_signed_order_path_evidence`,
/// `exact_wide_order_path_evidence`) read only the edges a node can take
/// from here, instead of every order fact at every node.
///
/// An `int32` fact `lower < upper` (or `<=`, after
/// [`condition_as_order_fact`]'s normalization) is filed under its written
/// `lower` and its canonical form; when `lower` is a constant also under
/// its value, so a constant
/// node finds every edge whose lower end is a constant at least as large by
/// one range read; and when `lower` is a load also under its pointer and
/// kind, the only loads memory-derivation bridging relates to it. A 64-bit
/// or `uint32` fact is filed under its canonical lower end, per format
/// (`WIDE_ORDER_FORMATS`), as the format-indexed walk matches.
#[derive(Clone, Debug, Default)]
pub(crate) struct OrderFactsByLower {
    written: crate::persistent::PersistentMap<
        checked_scalar_facts::ScalarOperandKey,
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    canonical: crate::persistent::PersistentMap<
        checked_scalar_facts::ScalarOperandKey,
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    constant: imbl::OrdMap<i64, imbl::OrdSet<ConditionTerm>>,
    load: crate::persistent::PersistentMap<
        (Address, LoadKind),
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    wide: [crate::persistent::PersistentMap<
        checked_scalar_facts::ScalarOperandKey,
        crate::persistent::PersistentSet<ConditionTerm>,
    >; 3],
}

impl OrderFactsByLower {
    fn adjust(&mut self, condition: &ConditionTerm, value: bool) {
        fn file<K: Ord + Clone>(
            index: &mut crate::persistent::PersistentMap<
                K,
                crate::persistent::PersistentSet<ConditionTerm>,
            >,
            key: K,
            condition: &ConditionTerm,
        ) {
            let filed = index.get(&key).cloned().unwrap_or_default();
            let filed = filed.with_value(condition.clone());
            *index = if filed.is_empty() {
                index.without_key(&key)
            } else {
                index.with_inserted(key, filed)
            };
        }
        use checked_scalar_facts::ScalarOperandKey as Key;
        let Some(view) = retained_order_bounds::order_view(condition, value) else {
            return;
        };
        let lower = view.operands[0].operand_view();
        if view.format == MachineIntegerType::Int32 {
            if let Some(constant) = lower.word32_constant().map(|bits| i64::from(bits as i32)) {
                let mut filed = self.constant.get(&constant).cloned().unwrap_or_default();
                filed.insert(condition.clone());

                if filed.is_empty() {
                    self.constant.remove(&constant);
                } else {
                    self.constant.insert(constant, filed);
                }
            }
            if let Some((_, pointer, kind)) = lower.read() {
                file(&mut self.load, (pointer.clone(), kind), condition);
            }
            file(
                &mut self.canonical,
                Key::canonical(view.format, lower),
                condition,
            );
            file(
                &mut self.written,
                Key::for_format(view.format, lower),
                condition,
            );
        } else if let Some(kind) = condition_reasoning::WIDE_ORDER_FORMATS
            .iter()
            .position(|format| *format == view.format)
        {
            file(
                &mut self.wide[kind],
                Key::canonical(view.format, lower),
                condition,
            );
        }
    }

    /// The `int32` order facts written with lower end `lower`.
    pub(in crate::kernel) fn written_from_view<'a>(
        &'a self,
        lower: crate::kernel::MachineOperandView<'_>,
    ) -> impl Iterator<Item = &'a ConditionTerm> + use<'a> {
        self.written
            .get(&checked_scalar_facts::ScalarOperandKey::for_format(
                MachineIntegerType::Int32,
                lower,
            ))
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The `int32` order facts whose lower end has canonical form
    /// `canonical`.
    pub(crate) fn canonical_from<'a>(
        &'a self,
        canonical: &MachineTerm,
    ) -> impl Iterator<Item = &'a ConditionTerm> + 'a {
        self.canonical
            .get(&checked_scalar_facts::ScalarOperandKey::for_format(
                MachineIntegerType::Int32,
                crate::kernel::MachineOperandView::Legacy(canonical),
            ))
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The `int32` order facts whose lower end is a constant at least
    /// `constant`.
    pub(crate) fn constant_at_least(&self, constant: i64) -> impl Iterator<Item = &ConditionTerm> {
        self.constant
            .range(constant..)
            .flat_map(|(_, filed)| filed.iter())
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The `int32` order facts whose lower end is a load of `pointer` as
    /// `kind`, at any state.
    pub(crate) fn loads_of<'a>(
        &'a self,
        pointer: &Address,
        kind: LoadKind,
    ) -> impl Iterator<Item = &'a ConditionTerm> + 'a {
        self.load
            .get(&(pointer.clone(), kind))
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The order facts at `format`, one of
    /// [`condition_reasoning::WIDE_ORDER_FORMATS`], whose lower end has
    /// canonical form `lower`.
    pub(in crate::kernel) fn wide_from<'a>(
        &'a self,
        format: MachineIntegerType,
        lower: &checked_scalar_facts::ScalarOperandKey,
    ) -> impl Iterator<Item = &'a ConditionTerm> + 'a {
        let kind = condition_reasoning::WIDE_ORDER_FORMATS
            .iter()
            .position(|wide| *wide == format);
        kind.and_then(|kind| self.wide[kind].get(lower))
            .into_iter()
            .flat_map(crate::persistent::PersistentSet::iter)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }
}

/// A hash of an offset's structure that two state-equivalent offsets
/// (`address_offsets_state_equivalent`) always share: every
/// literal load stands for its kind alone, since two loads of one kind at
/// proven-equal addresses may match whatever their pointers and states,
/// and a sum's operands are taken in either order. Unequal offsets may
/// share one too; the shape only narrows the facts to check.
pub(in crate::kernel) fn offset_state_shape(offset: &AddressOffset) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    match offset {
        AddressOffset::Int32Scaled { value, byte_width } => (
            0u8,
            byte_width,
            operand_fingerprint(
                value.operand_view(),
                OperandFingerprintPolicy::MemoryState(true),
            ),
        )
            .hash(&mut hasher),
        AddressOffset::Add(left, right) => {
            let (left, right) = (offset_state_shape(left), offset_state_shape(right));
            (1u8, left.min(right), left.max(right)).hash(&mut hasher)
        }
        other => (2u8, other).hash(&mut hasher),
    }
    hasher.finish()
}

/// A shape a universal fact's conclusion takes, read through its binders,
/// implications and conjunctions. Two conditions `condition_matches` can
/// relate share one, and so do two propositions that are alpha-equivalent
/// or equal up to proven terms, so an instantiation or a match against a
/// goal reads only the universals filed under the goal's shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(in crate::kernel) enum UniversalConclusionKey {
    /// An `int32` equality.
    Equal,
    /// A strict `int32` order, either way round.
    StrictOrder,
    /// A non-strict `int32` order, either way round.
    Order,
    /// Signed `int32` addition overflow.
    OverflowAdd,
    /// A mathematical integer equality.
    IntegerEqual,
    /// A pointer value equality.
    PointerEqual,
    /// A pointer offset equality.
    OffsetEqual,
    /// Any other condition, which matches only itself.
    OtherCondition,
    /// A loadability fact.
    Loadable,
    /// A universal with none of the shapes above.
    Other,
}

impl UniversalConclusionKey {
    /// The shape `condition_matches` relates `condition` within.
    pub(in crate::kernel) fn of_condition(condition: &ConditionTerm) -> Self {
        match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                ..
            } => Self::Equal,
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation,
                ..
            } => match relation {
                CompareRelation::Equal => Self::Equal,
                CompareRelation::LessThan | CompareRelation::GreaterThan => Self::StrictOrder,
                CompareRelation::LessEqual | CompareRelation::GreaterEqual => Self::Order,
            },
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                ..
            } => Self::OverflowAdd,
            ConditionTerm::IntegerEqual(_, _) => Self::IntegerEqual,
            ConditionTerm::PointerEqual(_, _) => Self::PointerEqual,
            ConditionTerm::AddressOffsetEqual(_, _) => Self::OffsetEqual,
            _ => Self::OtherCondition,
        }
    }

    /// Every shape the conclusion of `proposition` takes, or `Other` when
    /// it takes none. The walk follows a universal's body, an implication's
    /// consequent and both conjuncts, as instantiation and condition
    /// matching do.
    pub(in crate::kernel) fn of(proposition: &Proposition) -> BTreeSet<Self> {
        fn collect(proposition: &Proposition, keys: &mut BTreeSet<UniversalConclusionKey>) {
            match proposition {
                Proposition::ForAll { body, .. } => collect(body, keys),
                Proposition::Implies(_, conclusion) => collect(conclusion, keys),
                Proposition::And(left, right) => {
                    collect(left, keys);
                    collect(right, keys);
                }
                Proposition::ConditionIs(condition, _) => {
                    keys.insert(UniversalConclusionKey::of_condition(
                        condition.native_compat(),
                    ));
                }
                Proposition::MemoryLoadable { .. } => {
                    keys.insert(UniversalConclusionKey::Loadable);
                }
                _ => {}
            }
        }
        let mut keys = BTreeSet::new();
        collect(proposition, &mut keys);
        if keys.is_empty() {
            keys.insert(Self::Other);
        }
        keys
    }
}

/// `map` with `member` added to the set under `key`.
fn with_adjusted_member<K: Ord + Clone, V: Ord + Clone>(
    map: &crate::persistent::PersistentMap<K, crate::persistent::PersistentSet<V>>,
    key: &K,
    member: &V,
) -> crate::persistent::PersistentMap<K, crate::persistent::PersistentSet<V>> {
    let bucket = map.get(key).cloned().unwrap_or_default();
    let bucket = bucket.with_value(member.clone());
    if bucket.is_empty() {
        map.without_key(key)
    } else {
        map.with_inserted(key.clone(), bucket)
    }
}

mod selected_facts;
pub(crate) use selected_facts::SelectedFacts;

#[cfg(test)]
mod diagnostic_sample_tests {
    use super::*;

    #[test]
    fn diagnostic_samples_preserve_order_counts_and_overlap_without_unbounded_limits() {
        for (conditions, propositions) in
            [(0, 0), (0, 40), (40, 0), (5, 40), (40, 5), (5, 5), (20, 20)]
        {
            let mut context = PureFactContext::new();
            for index in 0..conditions {
                context = context.assume_condition(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(Variable(660_000 + index)),
                        MachineTerm::constant(1000),
                    ),
                    true,
                );
            }
            for index in 0..propositions {
                context = context.assume_proposition(Proposition::Predicate {
                    name: format!("sample_{index:03}"),
                    arguments: Vec::new(),
                });
            }
            let all = context.pure_facts();
            for (first, last) in [
                (0, 0),
                (12, 0),
                (8, 24),
                (0, 32),
                (usize::MAX, usize::MAX),
                (4, usize::MAX),
            ] {
                let prefix = first.min(32);
                let suffix = last.min(32 - prefix);
                let end = prefix.min(all.len());
                let start = all.len().saturating_sub(suffix).max(end);
                let expected: Vec<_> = all[..end]
                    .iter()
                    .chain(all[start..].iter())
                    .cloned()
                    .collect();
                let ((sample, count), work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        context.diagnostic_fact_sample(first, last)
                    });
                assert_eq!(
                    sample, expected,
                    "{conditions}/{propositions}, {first}/{last}"
                );
                assert_eq!(count, all.len());
                assert!(
                    work <= 32,
                    "unbounded diagnostic request visited {work} facts"
                );
            }
        }
    }
}

#[cfg(test)]
mod contradictory_branch_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/contradictory_branches.rs");
}

#[cfg(test)]
mod context_restriction_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/context_restriction.rs");
}

#[cfg(test)]
mod root_bounds_tests;

#[cfg(test)]
mod view_alias_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/view_aliases.rs");
}

#[cfg(test)]
mod resource_alias_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/resource_aliases.rs");
}

#[cfg(test)]
mod condition_bucket_scaling_tests {
    use super::*;
    include!("../scaling_tests/kernel/assumptions/condition_buckets.rs");
}

/// A 32-bit order comparison stated in the other direction: `b > a` for
/// `a < b`, `b >= a` for `a <= b`, and back. One match on the root.
fn mirrored_order32(condition: &ConditionTerm) -> Option<ConditionTerm> {
    let ConditionTerm::Compare {
        format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    let relation = match relation {
        CompareRelation::LessThan => CompareRelation::GreaterThan,
        CompareRelation::LessEqual => CompareRelation::GreaterEqual,
        CompareRelation::GreaterThan => CompareRelation::LessThan,
        CompareRelation::GreaterEqual => CompareRelation::LessEqual,
        CompareRelation::Equal => return None,
    };
    Some(ConditionTerm::Compare {
        format: *format,
        relation,
        left: right.clone(),
        right: left.clone(),
    })
}

#[cfg(test)]
mod shared_load_atom_comparison_tests {
    use super::*;
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp};

    fn load_pair(ty: MachineIntegerType) -> (MachineTerm, MachineTerm, Variable, Variable) {
        let kind = match ty {
            MachineIntegerType::Int32 => LoadKind::Int32,
            MachineIntegerType::UInt32 => LoadKind::UInt32,
            MachineIntegerType::Int64 | MachineIntegerType::UInt64 => LoadKind::Bits64,
            MachineIntegerType::Int128 => LoadKind::Int128,
            MachineIntegerType::UInt128 => LoadKind::UInt128,
            _ => unreachable!(),
        };
        let load = |block: &str| {
            let memory = crate::kernel::intern_memory(SymbolicMemory::new().with_block(block, 16));
            let pointer = Address {
                base: block.into(),
                offset: AddressOffset::Constant(0),
            };
            let variable = crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &pointer,
                kind,
                ty.format().bits() / 8,
            );
            (
                MachineTerm::MemoryLoad(ProgramPoint::at(&memory), Box::new(pointer), kind),
                variable,
            )
        };
        let (left, a) = load("shared-left");
        let (right, b) = load("shared-right");
        assert_ne!(a, b);
        (left, right, a, b)
    }

    #[test]
    fn common_guard_exact_equality_precedes_load_authority() {
        use crate::kernel::{BooleanOperandView as B, KernelTermImport};
        let _session = crate::kernel::VerificationSession::enter();
        let (read, _, _, _) = load_pair(MachineIntegerType::Int32);
        let comparison = |format| ConditionTerm::Compare {
            format,
            relation: CompareRelation::Equal,
            left: Box::new(read.clone()),
            right: Box::new(MachineTerm::constant(0)),
        };
        let signed = comparison(MachineIntegerType::Int32);
        let unsigned = comparison(MachineIntegerType::UInt32);
        let a = KernelTermImport::default().condition(&signed);
        let b = KernelTermImport::default().condition(&unsigned);
        let no_authority = |_: &MachineTerm, _: &MachineTerm| false;
        assert!(conditions_equal_with_load_atoms(
            &signed,
            &unsigned,
            &no_authority
        ));
        assert!(boolean_operands_equal_with_load_atoms(
            B::Shared(&a),
            B::Shared(&a),
            &no_authority
        ));
        assert!(boolean_operands_equal_with_load_atoms(
            B::Shared(&a),
            B::Shared(&b),
            &no_authority
        ));
        assert!(boolean_operands_equal_with_load_atoms(
            B::Native(&signed),
            B::Shared(&b),
            &no_authority
        ));
    }

    #[test]
    fn common_composite_guards_do_not_inherit_load_matching_authority() {
        use crate::kernel::{BooleanOperandView as B, KernelTermImport};
        let _session = crate::kernel::VerificationSession::enter();
        let (a, b, _, _) = load_pair(MachineIntegerType::Int32);
        let atom = |value| ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(value),
            right: Box::new(MachineTerm::constant(0)),
        };
        let a = atom(a);
        let b = atom(b);
        for (a, b) in [
            (
                ConditionTerm::BoolEqual(Box::new(a.clone()), Box::new(a.clone())),
                ConditionTerm::BoolEqual(Box::new(b.clone()), Box::new(b.clone())),
            ),
            (
                ConditionTerm::BoolIf {
                    condition: Box::new(a),
                    then_condition: Box::new(ConditionTerm::Constant(true)),
                    else_condition: Box::new(ConditionTerm::Constant(false)),
                },
                ConditionTerm::BoolIf {
                    condition: Box::new(b),
                    then_condition: Box::new(ConditionTerm::Constant(true)),
                    else_condition: Box::new(ConditionTerm::Constant(false)),
                },
            ),
        ] {
            let ar = KernelTermImport::default().condition(&a);
            let br = KernelTermImport::default().condition(&b);
            assert!(!conditions_equal_with_load_atoms(&a, &b, &|_, _| true));
            assert!(!boolean_operands_equal_with_load_atoms(
                B::Shared(&ar),
                B::Shared(&br),
                &|_, _| true
            ));
            assert!(!boolean_operands_equal_with_load_atoms(
                B::Native(&a),
                B::Shared(&br),
                &|_, _| true
            ));
        }
    }

    #[test]
    fn shared_comparisons_require_the_current_load_atom_authority() {
        for structural in [false, true] {
            for ty in [
                MachineIntegerType::Int32,
                MachineIntegerType::UInt32,
                MachineIntegerType::Int64,
                MachineIntegerType::UInt64,
                MachineIntegerType::Int128,
                MachineIntegerType::UInt128,
            ] {
                let _session = crate::kernel::VerificationSession::enter();
                let (left_load, right_load, a, b) = load_pair(ty);
                let variable = |v| {
                    if structural {
                        crate::kernel::KernelTermImport::default()
                            .machine_arithmetic(ty, &MachineTerm::Variable(v))
                            .unwrap()
                    } else {
                        KernelTerm::variable(KernelType::Program(ty.program_type()), v)
                    }
                };
                let product = |v, op| {
                    KernelTerm::machine_binary_shared(
                        ty,
                        op,
                        [variable(v), variable(Variable(990001))],
                    )
                };
                let root = product(a, MachineBinaryOp::Multiply);
                let observed = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
                let condition = |term| {
                    ConditionTerm::integer_less_equal(
                        IntegerTerm::Machine(
                            SharedMachineIntegerTerm::from_shared(ty, term).unwrap(),
                        ),
                        IntegerTerm::constant_i64(7),
                    )
                };
                let left = condition(root);
                let right = condition(product(b, MachineBinaryOp::Multiply));
                let wrong = condition(product(b, MachineBinaryOp::Add));
                let exports = KernelTermExport::machine_export_count();
                let calls = std::cell::Cell::new(0);
                let accept = |l: &MachineTerm, r: &MachineTerm| {
                    if let (MachineTerm::Variable(left), MachineTerm::Variable(right)) = (l, r) {
                        assert_eq!((*left, *right), (a, b));
                        // This authority recognizes origin states only. The
                        // optional named-load check must still consult it.
                        return false;
                    }
                    calls.set(calls.get() + 1);
                    assert_eq!(l, &left_load);
                    assert_eq!(r, &right_load);
                    true
                };
                assert!(conditions_equal_with_load_atoms(&left, &right, &accept));
                assert_eq!(calls.get(), 1);
                assert!(!conditions_equal_with_load_atoms(&left, &right, &|_, _| {
                    false
                }));
                assert!(!conditions_equal_with_load_atoms(&left, &wrong, &|_, _| {
                    true
                }));
                assert!(
                    !PureFactContext::new().conditions_equal_modulo_proven_states(&left, &right)
                );
                let mixed = MachineTerm::Binary {
                    format: ty,
                    op: MachineBinaryOp::Multiply,
                    left: Box::new(right_load.clone()),
                    right: Box::new(MachineTerm::Variable(Variable(990001))),
                };
                let mixed = ConditionTerm::Compare {
                    format: ty,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(mixed),
                    right: Box::new(MachineTerm::machine_constant(
                        crate::kernel::MachineIntegerConstant::from_signed(ty.format(), 7).unwrap(),
                    )),
                };
                assert!(
                    conditions_equal_with_load_atoms(&left, &mixed, &accept),
                    "{ty:?}: {left:?} / {mixed:?}"
                );
                assert!(!conditions_equal_with_load_atoms(&left, &mixed, &|_, _| {
                    false
                }));
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert!(!observed.has_boxed_operand());
            }
        }
    }

    #[test]
    fn shared_state_premise_requires_the_selected_frame() {
        use crate::kernel::proof::PureFactStore;
        let _session = crate::kernel::VerificationSession::enter();
        let before = SymbolicMemory::new()
            .with_block("shared-frame", 8)
            .with_block("call-havoc:0", 0);
        let after = before.clone().with_block("call-havoc:1", 0);
        let loaded = Address {
            base: "shared-frame".into(),
            offset: AddressOffset::Constant(0),
        };
        let elsewhere = Address {
            base: "elsewhere".into(),
            offset: AddressOffset::Constant(0),
        };
        let effect = Proposition::MemoryEffectSummary {
            before: before.clone(),
            after: after.clone(),
            mutable_ranges: vec![MemoryRange::new(elsewhere, 0u32.into(), 1u32.into())],
        };
        let (_, _, equality) = crate::kernel::tests::explicit_frame(
            &before,
            &after,
            &loaded,
            ProgramType::Int32,
            &[effect],
            &PureFactContext::new(),
        )
        .expect("disjoint selected footprint");
        let condition = |memory: &SymbolicMemory| {
            let memory = crate::kernel::intern_memory(memory.clone());
            let variable = crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &loaded,
                LoadKind::Int32,
                4,
            );
            let root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Multiply,
                [
                    KernelTerm::variable(KernelType::Program(ProgramType::Int32), variable),
                    KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(990002)),
                ],
            );
            ConditionTerm::integer_less_equal(
                IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap(),
                ),
                IntegerTerm::constant_i64(7),
            )
        };
        let (source, truth) =
            crate::kernel::machine_integer::comparison::native_comparison_of_integer_observation(
                &condition(&before),
                true,
            )
            .unwrap();
        let source = Proposition::condition_is(source, truth);
        let target = Proposition::condition_is(condition(&after), true);
        for source in std::iter::once(Proposition::condition_is(condition(&before), true)).chain(
            crate::kernel::proof::fact_reasoning::order_claim_forms(&source),
        ) {
            let unframed = PureFactStore::from_ordered(std::slice::from_ref(&source));
            let framed = PureFactStore::from_ordered(&[source.clone(), equality.clone()]);
            let exports = KernelTermExport::machine_export_count();
            assert!(!unframed.exact_available_across_effects(&target, &[]));
            let available = framed.exact_available_across_effects(&target, &[]);
            if !available {
                // Reference the existing certificate adapter: these premises
                // must remain available when its boxed query is removed.
                let Proposition::ConditionIs(condition, truth) = &target else {
                    unreachable!()
                };
                let (native, truth) = crate::kernel::machine_integer::comparison::native_comparison_of_integer_observation(condition.native_compat(), *truth).unwrap();
                let native = Proposition::condition_is(native, truth);
                assert!(
                    crate::kernel::proof::fact_reasoning::order_claim_forms(&native)
                        .iter()
                        .any(|p| framed.exact_available_across_effects(p, &[])),
                    "legacy certificate route must supply the control"
                );
            }
            assert!(available, "missing shared premise: {source:?}");
            assert!(!unframed.exact_available_across_effects(&target, &[]));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
        use crate::kernel::machine_integer::{
            Operation, comparison::native_comparison_view, definedness::OverflowQueryView,
        };
        let (native, _) =
            crate::kernel::machine_integer::comparison::native_comparison_of_integer_observation(
                &condition(&before),
                true,
            )
            .unwrap();
        let ConditionTerm::Compare { left, .. } = native else {
            unreachable!()
        };
        let factor = MachineTerm::Variable(Variable(991010));
        let source = Proposition::condition_is(
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Multiply,
                left,
                right: Box::new(factor.clone()),
            },
            false,
        );
        let missing_frame = PureFactStore::from_ordered(std::slice::from_ref(&source));
        let framed = PureFactStore::from_ordered(&[source, equality]);
        let later = condition(&after);
        let view = native_comparison_view(&later, true).unwrap();
        let query = OverflowQueryView::from_operands(
            MachineIntegerType::Int32,
            Operation::Multiply,
            [
                view.operands[0].operand_view(),
                MachineOperandView::Legacy(&factor),
            ],
        )
        .unwrap();
        let exports = KernelTermExport::machine_export_count();
        for bound in query.bounds() {
            assert!(!missing_frame.listed_premise_available(&bound, &[], false));
            assert!(framed.listed_premise_available(&bound, &[], false));
            assert!(!missing_frame.listed_premise_available(&bound, &[], false));
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn held_nonoverflow_sources_supply_shared_bounds_without_export() {
        use crate::kernel::machine_integer::{
            Operation,
            definedness::{OverflowQueryView, defined_formats},
        };
        use crate::kernel::proof::PureFactStore;
        for ty in defined_formats() {
            for (operation, op) in [
                (Operation::Add, OverflowOperation::Add),
                (Operation::Subtract, OverflowOperation::Subtract),
                (Operation::Multiply, OverflowOperation::Multiply),
            ] {
                let _session = crate::kernel::VerificationSession::enter();
                let native = MachineTerm::Binary {
                    format: ty,
                    op: MachineBinaryOp::Multiply,
                    left: Box::new(MachineTerm::Variable(Variable(991001))),
                    right: Box::new(MachineTerm::Variable(Variable(991002))),
                };
                let source = |op, truth| {
                    Proposition::condition_is(
                        ConditionTerm::Overflows {
                            format: ty,
                            op,
                            left: Box::new(native.clone()),
                            right: Box::new(MachineTerm::Variable(Variable(991003))),
                        },
                        truth,
                    )
                };
                let held = PureFactStore::from_ordered(&[source(op, false)]);
                let missing = PureFactStore::from_ordered(&[]);
                let refuted = PureFactStore::from_ordered(&[source(op, true)]);
                let wrong = PureFactStore::from_ordered(&[source(
                    if op == OverflowOperation::Add {
                        OverflowOperation::Multiply
                    } else {
                        OverflowOperation::Add
                    },
                    false,
                )]);
                let variable =
                    |id| KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
                let root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Multiply,
                    [variable(991001), variable(991002)],
                );
                let right = variable(991003);
                let query = OverflowQueryView::from_operands(
                    ty,
                    operation,
                    [
                        MachineOperandView::Shared(&root),
                        MachineOperandView::Shared(&right),
                    ],
                )
                .unwrap();
                let exports = KernelTermExport::machine_export_count();
                for bound in query.bounds() {
                    assert!(
                        held.listed_premise_available(&bound, &[], false),
                        "{ty:?} {operation:?}"
                    );
                    assert!(!missing.listed_premise_available(&bound, &[], false));
                    assert!(!refuted.listed_premise_available(&bound, &[], false));
                    assert!(!wrong.listed_premise_available(&bound, &[], false));
                }
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                for operand in &query.operands {
                    let crate::kernel::machine_integer::comparison::ComparisonOperand::Observation(
                        observation,
                    ) = operand
                    else {
                        unreachable!()
                    };
                    // Fixed-size atom adapters may retain a native variable;
                    // symbolic arithmetic must never acquire a boxed tree.
                    if observation.operand_view().binary().is_some() {
                        assert!(!observation.has_boxed_operand(), "{ty:?} {operation:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn shared_fact_matching_preserves_native_comparison_identities() {
        let _session = crate::kernel::VerificationSession::enter();
        let (_, _, a, b) = load_pair(MachineIntegerType::Int32);
        let forms = |variable| {
            let mut forms = Vec::new();
            for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
                for relation in [
                    CompareRelation::Equal,
                    CompareRelation::LessThan,
                    CompareRelation::LessEqual,
                    CompareRelation::GreaterThan,
                    CompareRelation::GreaterEqual,
                ] {
                    for constant in [
                        MachineTerm::constant(u32::MAX),
                        MachineTerm::constant_at32(MachineIntegerType::Int32, u32::MAX),
                        MachineTerm::constant_at32(MachineIntegerType::UInt32, u32::MAX),
                    ] {
                        forms.push(ConditionTerm::Compare {
                            format,
                            relation,
                            left: Box::new(MachineTerm::Variable(variable)),
                            right: Box::new(constant),
                        });
                    }
                }
            }
            forms
        };
        for left in forms(a) {
            for right in forms(b) {
                let (lo, ll, lr) = left.as_fact_comparison().unwrap();
                let (ro, rl, rr) = right.as_fact_comparison().unwrap();
                let expected = lo == ro
                    && terms_equal_with_load_atoms(&ll, &rl, &|_, _| true)
                    && terms_equal_with_load_atoms(&lr, &rr, &|_, _| true);
                assert_eq!(
                    conditions_equal_with_load_atoms(&left, &right, &|_, _| true),
                    expected,
                    "{left:?} / {right:?}"
                );
            }
        }
    }

    mod scaling_tests {
        include!("../scaling_tests/kernel/assumptions/shared_load_atom_comparison_tests.rs");
    }
}

#[cfg(test)]
mod shared_read_memory_collection_tests {
    use super::*;

    #[test]
    fn shared_read_collection_preserves_width_and_state_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new().with_block("read-width", 8);
        let pointer = Address {
            base: AddressBase::Concrete("read-width".into()),
            offset: AddressOffset::Constant(0),
        };
        let raw = MachineTerm::MemoryLoad(
            ProgramPoint::at(&(intern_memory(memory.clone()))),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let narrow = MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: MachineIntegerType::Int8,
            to: MachineIntegerType::Int32,
            value: Box::new(raw.clone()),
        };
        let wide = MachineTerm::Binary {
            format: MachineIntegerType::Int64,
            op: MachineBinaryOp::Add,
            left: Box::new(raw.clone()),
            right: Box::new(raw.clone()),
        };
        let specialized = MachineTerm::Cast {
            spelling: MachineCastSpelling::Int64From32,
            from: MachineIntegerType::Int32,
            to: MachineIntegerType::Int64,
            value: Box::new(raw.clone()),
        };
        let changed = memory
            .clone()
            .store(pointer, ProgramValue::Int32(MachineTerm::constant(9)));
        let mut cases = vec![raw.clone(), narrow, wide, specialized];
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
            MachineIntegerType::Int128,
            MachineIntegerType::UInt128,
        ] {
            cases.push(MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: Box::new(raw.clone()),
                right: Box::new(raw.clone()),
            });
        }
        for native in cases {
            let root = KernelTermImport::default().machine(MachineIntegerType::Int64, &native);
            for current in [&memory, &changed] {
                for width in [None, Some(2), Some(4), Some(8)] {
                    let mut expected = Vec::new();
                    let native_result = collect_bitvector_memory_loads_with_width(
                        &native,
                        current,
                        &mut expected,
                        width,
                        &mut BTreeSet::new(),
                    );
                    let mut actual = Vec::new();
                    let exports = KernelTermExport::machine_export_count();
                    let shared_result = collect_shared_read_memory_loads(
                        &root,
                        current,
                        &mut actual,
                        width,
                        &mut BTreeSet::new(),
                    );
                    assert_eq!(shared_result, native_result);
                    expected.sort();
                    expected.dedup();
                    actual.sort();
                    actual.dedup();
                    assert_eq!(actual, expected);
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }
}

#[cfg(test)]
mod pointer_index_walk_tests {
    use super::*;
    use crate::kernel::{KernelTermExport, KernelTermImport, VerificationSession};

    fn offset(machine: SharedMachineIntegerTerm) -> AddressOffset {
        if machine.ty().format().bits() == 32 {
            AddressOffset::Int32Scaled {
                value: machine,
                byte_width: 4,
            }
        } else {
            let unsigned = machine.ty() == MachineIntegerType::UInt64;
            AddressOffset::Int64Scaled {
                value: machine,
                byte_width: 8,
                unsigned,
            }
        }
    }

    #[test]
    fn pointer_index_reads_and_fingerprints_preserve_native_rules() {
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let _session = VerificationSession::enter();
            let memory = SymbolicMemory::new().with_block("r7-read", 8);
            let address = Address {
                base: AddressBase::Concrete("r7-read".into()),
                offset: AddressOffset::Constant(0),
            };
            let old = intern_memory(memory.clone());
            let changed = memory.clone().store(
                address.clone(),
                ProgramValue::Int32(MachineTerm::constant(7)),
            );
            let mut fingerprints = Vec::new();
            let mut previous = None;
            for retained_state in [old, intern_memory(changed.clone())] {
                let native = MachineTerm::Binary {
                    format: ty,
                    op: MachineBinaryOp::Add,
                    left: MachineTerm::Variable(Variable(1007210)).into(),
                    right: MachineTerm::MemoryLoad(
                        ProgramPoint::at(&retained_state),
                        address.clone().into(),
                        LoadKind::Int32,
                    )
                    .into(),
                };
                let root = KernelTermImport::default()
                    .machine_arithmetic(ty, &native)
                    .unwrap();
                let shared = offset(SharedMachineIntegerTerm::from_shared(ty, root).unwrap());
                let legacy = offset(SharedMachineIntegerTerm::intern(ty, native.clone()));
                let before = KernelTermExport::machine_export_count();
                let shared_view = match &shared {
                    AddressOffset::Int32Scaled { value, .. }
                    | AddressOffset::Int64Scaled { value, .. } => value.operand_view(),
                    _ => unreachable!(),
                };
                assert_eq!(
                    memory_blind_operand_fingerprint(shared_view),
                    memory_blind_operand_fingerprint(MachineOperandView::Legacy(&native)),
                );
                assert!(operands_equal_with_load_atoms(
                    ty,
                    shared_view,
                    MachineOperandView::Legacy(&native),
                    &|a, b| a == b,
                ));
                for current in [&memory, &changed] {
                    let (mut actual, mut expected) = (Vec::new(), Vec::new());
                    let a = collect_pointer_offset_memory_loads(
                        &shared,
                        current,
                        &mut actual,
                        &mut BTreeSet::new(),
                    );
                    let b = collect_bitvector_memory_loads(
                        &native,
                        current,
                        &mut expected,
                        Some(ty.format().bits() / 8),
                        &mut BTreeSet::new(),
                    );
                    assert_eq!(a, b);
                    assert_eq!(actual, expected);
                }
                let pointer = |offset| Address {
                    base: AddressBase::Concrete("r7-index".into()),
                    offset,
                };
                let hash = memory_blind_pointer_fingerprint(&pointer(shared.clone()));
                assert_eq!(
                    hash,
                    memory_blind_pointer_fingerprint(&pointer(legacy.clone()))
                );
                fingerprints.push(hash);
                let loads_match = |a: &MachineTerm, b: &MachineTerm| a == b;
                assert!(offsets_equal_with_load_atoms(
                    &shared,
                    &shared,
                    &loads_match
                ));
                if ty == MachineIntegerType::Int32 {
                    assert!(offsets_equal_with_load_atoms(
                        &shared,
                        &legacy,
                        &loads_match
                    ));
                    assert!(offsets_equal_with_load_atoms(
                        &legacy,
                        &shared,
                        &loads_match
                    ));
                    if let Some(previous) = &previous {
                        assert!(!offsets_equal_with_load_atoms(
                            &shared,
                            previous,
                            &|_, _| false
                        ));
                        assert!(offsets_equal_with_load_atoms(&shared, previous, &|_, _| {
                            true
                        }));
                    }
                    previous = Some(shared.clone());
                }
                assert_eq!(KernelTermExport::machine_export_count(), before);
            }
            assert_eq!(
                fingerprints[0], fingerprints[1],
                "states do not affect the fingerprint"
            );
        }
    }

    mod scaling_tests {
        use super::*;
        include!("../scaling_tests/kernel/assumptions/pointer_index_walks.rs");
    }
}

pub(in crate::kernel) fn signed_index_constant(view: MachineOperandView<'_>) -> Option<i64> {
    view.word32_constant().map(|word| i64::from(word as i32))
}

pub(in crate::kernel) fn index_comparison(
    relation: CompareRelation,
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> ConditionTerm {
    crate::kernel::machine_integer::comparison::condition_for_operand_views(
        MachineIntegerType::Int32,
        relation,
        [left, right],
    )
}

pub(in crate::kernel) fn wide_index_comparison(
    relation: CompareRelation,
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> ConditionTerm {
    crate::kernel::machine_integer::comparison::condition_for_operand_views(
        MachineIntegerType::UInt64,
        relation,
        [left, right],
    )
}

pub(in crate::kernel) fn wide_index_binary(
    op: MachineBinaryOp,
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> SharedMachineIntegerTerm {
    // Fixed-size literals need neither prefix import nor the arithmetic memo.
    // Construct their retained result directly so cold and warm queries pay
    // the same work, just as the native literal operation does.
    if let (Some(left), Some(right)) = (left.uint64_constant(), right.uint64_constant()) {
        let value = MachineTerm::machine_binary(
            MachineIntegerType::UInt64,
            op,
            MachineTerm::uint64_constant(left),
            MachineTerm::uint64_constant(right),
        );
        let root = KernelTerm::retained_native_machine_operand(MachineIntegerType::UInt64, &value);
        return MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt64);
    }
    let root = crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
        MachineIntegerType::UInt64,
        op,
        KernelTerm::retained_machine_operand(MachineIntegerType::UInt64, left),
        KernelTerm::retained_machine_operand(MachineIntegerType::UInt64, right),
    );
    MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt64)
}

pub(in crate::kernel) fn index_binary(
    op: MachineBinaryOp,
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> SharedMachineIntegerTerm {
    if let (Some(left), Some(right)) = (left.word32_constant(), right.word32_constant()) {
        return SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::machine_binary(
                MachineIntegerType::Int32,
                op,
                MachineTerm::constant(left),
                MachineTerm::constant(right),
            ),
        );
    }
    if op == MachineBinaryOp::Subtract
        && let (MachineOperandView::Shared(a), MachineOperandView::Shared(b)) = (left, right)
        && a == b
    {
        return SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::constant(0),
        );
    }
    let root = crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
        MachineIntegerType::Int32,
        op,
        KernelTerm::retained_machine_operand(MachineIntegerType::Int32, left),
        KernelTerm::retained_machine_operand(MachineIntegerType::Int32, right),
    );
    MachineOperandView::Shared(&root).retain(MachineIntegerType::Int32)
}

/// Walk each retained node once, then propagate coefficients in DAG order.
/// Atom keys use the same fact-free canonical reading as the native affine walk.
fn affine_index_terms_views(
    inputs: &[(MachineOperandView<'_>, i64)],
) -> Option<(BTreeMap<checked_scalar_facts::ScalarOperandKey, i64>, i64)> {
    use MachineIntegerType::Int32;
    let roots: Vec<_> = inputs.iter().map(|(v, c)| (v.retain(Int32), *c)).collect();
    let mut pending: Vec<_> = roots.iter().map(|(v, _)| (v.clone(), false)).collect();
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    let mut edges = BTreeMap::new();
    while let Some((term, finish)) = pending.pop() {
        if finish {
            order.push(term);
            continue;
        }
        if !seen.insert(term.clone()) {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        let children = match term.operand_view().binary() {
            Some((Int32, MachineBinaryOp::Add, [a, b])) => {
                vec![(a.retain(Int32), 1), (b.retain(Int32), 1)]
            }
            Some((Int32, MachineBinaryOp::Subtract, [a, b])) => {
                vec![(a.retain(Int32), 1), (b.retain(Int32), -1)]
            }
            Some((Int32, MachineBinaryOp::Multiply, [a, b])) => {
                if let Some(c) = signed_index_constant(a) {
                    vec![(b.retain(Int32), c)]
                } else {
                    vec![(a.retain(Int32), signed_index_constant(b)?)]
                }
            }
            _ => vec![],
        };
        pending.push((term.clone(), true));
        pending.extend(children.iter().map(|(child, _)| (child.clone(), false)));
        edges.insert(term, children);
    }
    let mut coefficients = BTreeMap::<SharedMachineIntegerTerm, i64>::new();
    for (root, coefficient) in roots {
        let entry = coefficients.entry(root).or_default();
        *entry = entry.checked_add(coefficient)?;
    }
    let mut atoms = BTreeMap::<checked_scalar_facts::ScalarOperandKey, i64>::new();
    let mut constant = 0i64;
    for term in order.into_iter().rev() {
        let coefficient = coefficients.remove(&term).unwrap_or(0);
        if coefficient == 0 {
            continue;
        }
        let children = edges.remove(&term)?;
        if !children.is_empty() {
            for (child, scale) in children {
                let entry = coefficients.entry(child).or_default();
                *entry = entry.checked_add(coefficient.checked_mul(scale)?)?;
            }
        } else if let Some(value) = signed_index_constant(term.operand_view()) {
            constant = constant.checked_add(coefficient.checked_mul(value)?)?;
        } else {
            let key = checked_scalar_facts::ScalarOperandKey::canonical(Int32, term.operand_view());
            let entry = atoms.entry(key).or_default();
            *entry = entry.checked_add(coefficient)?;
        }
    }
    atoms.retain(|_, coefficient| *coefficient != 0);
    Some((atoms, constant))
}

pub(in crate::kernel) fn affine_bitvector_difference_constant_views(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> Option<i64> {
    // Fixed-size inputs need no DAG allocation or import. In particular,
    // literal bounds are queried once per cached cell during a store.
    if let (Some(left), Some(right)) = (signed_index_constant(left), signed_index_constant(right)) {
        return Some(left - right);
    }
    match (left.variable(), right.variable()) {
        (Some(left), Some(right)) => return (left == right).then_some(0),
        (Some(_), None) if signed_index_constant(right).is_some() => return None,
        (None, Some(_)) if signed_index_constant(left).is_some() => return None,
        _ => {}
    }
    if let (MachineOperandView::Shared(left), MachineOperandView::Shared(right)) = (left, right)
        && left == right
    {
        return Some(0);
    }
    let (atoms, constant) = affine_index_terms_views(&[(left, 1), (right, -1)])?;
    atoms.is_empty().then_some(constant)
}

/// Whether an element-index term is known nonnegative, by exact routes only:
/// its own constant value, or the same order routes a stated span guard is
/// checked by. This is the premise that keeps a 32-bit subtraction of two
/// indices inside `int32`, which several conclusions below need and none may
/// assume.
pub(in crate::kernel) fn element_index_is_nonnegative_view(
    term: MachineOperandView<'_>,
    assumptions: Option<&PureFactContext>,
) -> bool {
    signed_index_constant(term).is_some_and(|value| value >= 0)
        || assumptions.is_some_and(|a| {
            a.proves_element_endpoint_order_views(
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
                term,
            )
        })
}

/// Whether an affine constant difference between two element-index terms is
/// their true difference in `i64`, and not merely that difference modulo
/// `2^32`.
///
/// This is the premise every *positive* membership conclusion needs and no
/// negative one does, and it is the whole difference between the two. Write
/// `D = sext(index) - sext(start)` for the true difference and `r` for the
/// residue the affine walk yields. Both terms are `int32`, so `D` lies in
/// `(-2^32, 2^32)`, and `D ≡ r (mod 2^32)` pins it to `D ∈ {r, r - 2^32}`.
///
/// "Outside" needs no more: `r - 2^32` is negative, so below the start, and `r`
/// above the count is past the end — outside under either reading, which is
/// what [`affine_offset_from_start_is_outside`] uses. "Inside" needs `D = r`
/// outright, because `D = r - 2^32` is *outside*. `i + 1` is one element above
/// `i` only while the add does not wrap; at `i == i32::MAX` it is `2^32 - 1`
/// elements below.
///
/// Three routes rule the wrapped reading out, and each is checked before any
/// fact lookup.
///
/// * `r == 0`. Then `D` is `0` or `-2^32`, and `-2^32` is out of reach, so the
///   two terms name the same element. This is the route that carries the
///   ordinary shapes — a child range starting where its parent does, a pointer
///   at a range's own start — with no context at all.
/// * `r` in the upper half is refused. `D = r >= 2^31` would need the index
///   `2^31` elements above the start, and a range that reaches that far fails
///   its valid-span guard, so a membership caller cannot want it; refusing
///   costs nothing and keeps the argument below to the low half.
/// * Otherwise `D = r - 2^32 <= -2^31 - 1`, which forces `sext(index) < 0` and
///   `sext(start) > 0` together: with `sext(index) >= 0` the difference is at
///   least `-sext(start) > -2^31`, and with `sext(start) <= 0` it is at least
///   `sext(index) >= -2^31`. So *either* `0 <= index` *or* `start <= 0`
///   excludes it. A constant endpoint settles its own side without consulting
///   anything, which is why a range over `p[0..n]` and a constant index need no
///   facts; otherwise the order comes from the same exact routes a stated
///   span guard is checked by.
///
/// Default-deny: a caller with no context gets the fact-free routes only.
/// Two constant endpoints also determine a negative difference directly.
pub(in crate::kernel) fn exact_affine_index_difference_views(
    index: MachineOperandView<'_>,
    start: MachineOperandView<'_>,
    assumptions: Option<&PureFactContext>,
) -> Option<i64> {
    if let (Some(index), Some(start)) = (signed_index_constant(index), signed_index_constant(start))
    {
        return Some(index - start);
    }
    let residue = affine_bitvector_difference_constant_views(index, start)?.rem_euclid(1i64 << 32);
    if residue == 0 {
        return Some(0);
    }
    if residue >= 1i64 << 31 {
        return None;
    }
    (element_index_is_nonnegative_view(index, assumptions)
        || signed_index_constant(start).is_some_and(|s| s <= 0)
        || assumptions.is_some_and(|a| {
            a.proves_element_endpoint_order_views(
                start,
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
            )
        }))
    .then_some(residue)
}

fn held_index_add_nonoverflow(
    a: &PureFactContext,
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> bool {
    if let (Some(l), Some(r)) = (left.word32_constant(), right.word32_constant()) {
        return !(l as i32).overflowing_add(r as i32).1;
    }
    let query = crate::kernel::machine_integer::definedness::OverflowQueryView::from_operands(
        MachineIntegerType::Int32,
        crate::kernel::machine_integer::Operation::Add,
        [left, right],
    )
    .expect("int32 addition");
    a.contains_known_overflow_query(&query, false)
}

fn affine_range_element_count_views(
    start: MachineOperandView<'_>,
    end: MachineOperandView<'_>,
) -> Option<i64> {
    let residue = affine_bitvector_difference_constant_views(end, start)?.rem_euclid(1i64 << 32);
    (residue < (1i64 << 31)).then_some(residue)
}

fn affine_bitvector_difference_atom_views(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> Option<SharedMachineIntegerTerm> {
    let (atoms, constant) = affine_index_terms_views(&[(left, 1), (right, -1)])?;
    if constant != 0 || atoms.len() != 1 {
        return None;
    }
    let (atom, coefficient) = atoms.into_iter().next()?;
    (coefficient == 1).then(|| atom.operand_view().retain(MachineIntegerType::Int32))
}
