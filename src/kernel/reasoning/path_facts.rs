use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::binary_term;
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int64_constant, uint64_constant,
};

/// Whether a memory fact about `base` established in `range_memory` still
/// describes an available region in `current_memory`: the block must be
/// present in both or absent in both, and no heap allocation that may
/// contain `base` may have been freed in one state but not the other.
/// The second condition is what distinguishes the states for an
/// `ExternalArgument` allocation, whose block survives `free`.
pub(in crate::kernel) fn memory_range_still_available(
    range_memory: &SymbolicMemory,
    current_memory: &SymbolicMemory,
    base: &Address,
    assumptions: &PureFactContext,
) -> bool {
    // A pointer read's synthetic block is not the storage it designates.
    // Use its one defining store, when present, for the lifetime comparison.
    let stored = crate::kernel::eval::pointer_read_over_immediate_store(base);
    let base = stored.as_ref().unwrap_or(base);
    range_memory == current_memory
        || range_memory.has_block(&base.base) == current_memory.has_block(&base.base)
            && range_memory.is_ended_local_address(base)
                == current_memory.is_ended_local_address(base)
            && (range_memory.shares_heap_deallocations_with(current_memory)
                || range_memory.is_deallocated_heap_address(base, assumptions)
                    == current_memory.is_deallocated_heap_address(base, assumptions))
}

#[cfg(test)]
pub(in crate::kernel) fn forall_int32(var: Variable, body: Proposition) -> Proposition {
    crate::kernel::quantifiers::test_forall(Default::default(), var, Sort::ProgramInt32, body)
}

pub(in crate::kernel) fn wrap_proof_facts(
    proposition: Proposition,
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> Proposition {
    wrap_ambient_proof_facts(
        wrap_local_proof_facts(proposition, facts, obligations),
        &assumptions.prop_facts,
        &assumptions.condition_facts,
    )
}

pub(in crate::kernel) fn wrap_local_proof_facts(
    proposition: Proposition,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    facts
        .fact_iter()
        .filter(|fact| fact.is_public())
        .filter(|fact| {
            !fact.is_logical_read_equation()
                && !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition())
        })
        .rev()
        .fold(proposition, |body, fact| {
            Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
        })
}

pub(in crate::kernel) fn wrap_ambient_proof_facts(
    proposition: Proposition,
    propositions: &crate::kernel::fact_collections::FactSet<Proposition>,
    conditions: &crate::kernel::fact_collections::FactMap<ConditionTerm, bool>,
) -> Proposition {
    let proposition = propositions
        .scan_for_upkeep()
        .rev()
        .fold(proposition, |body, proposition| {
            Proposition::Implies(Box::new(proposition.clone()), Box::new(body))
        });

    conditions
        .scan_for_upkeep()
        .rev()
        .fold(proposition, |body, (condition, value)| {
            Proposition::Implies(
                Box::new(Proposition::condition_is(condition.clone(), *value)),
                Box::new(body),
            )
        })
}

/// Why one node at the head of a lowered proposition exists.
///
/// Lowering is not an isomorphism from written Surface syntax to kernel
/// propositions: it inserts `Implies` nodes that no Surface connective
/// wrote, guarding a body with a path fact the lowering established or with
/// a load obligation the state did not discharge. A proof step that
/// introduces the head of a lowered goal must know which kind of node it is
/// reaching, because only a written connective consumes a written Surface
/// connective, and a written universal binds a written Surface name to the
/// exact kernel variable the lowering chose.
///
/// One value describes one node. The head chain of a lowered proposition,
/// outermost first, is a [`LoweringIntroductions`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoweringIntroduction {
    /// An `Implies` inserted by lowering to guard the body with a path fact
    /// the lowering established. No Surface connective corresponds to it.
    PathFactGuard,
    /// An `Implies` inserted by lowering to guard the body with a path
    /// obligation. No Surface connective corresponds to it.
    ObligationGuard,
    /// An `Implies` written as a spec, and therefore Surface, implication.
    WrittenImplication,
    /// A `Not` written as a spec, and therefore Surface, negation.
    WrittenNegation,
    /// A `Not` introduced by lowering a written `!=` comparison. The source
    /// has no separate negation connective to consume.
    ComparisonNegation,
    /// A `ForAll` written as a spec, and therefore Surface, universal.
    /// `name` is the written binder spelling and `variable` is the exact
    /// kernel variable the lowering bound it to.
    WrittenUniversal {
        name: BindingName,
        variable: Variable,
        pointer: bool,
        integer: bool,
    },
}

/// The head chain of a lowered proposition, outermost first: one entry per
/// node reachable through introductions before any other step. A negation
/// marks the end of that chain.
pub type LoweringIntroductions = Vec<LoweringIntroduction>;

pub(in crate::kernel) fn wrap_path_context(
    proposition: Proposition,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> Proposition {
    wrap_path_context_with_introductions(proposition, facts, obligations).0
}

/// [`wrap_path_context`], also reporting the guard nodes it inserted, in the
/// order they appear from the outside in. Both results come from one
/// traversal under one filter, so the record cannot drift from the
/// proposition it describes.
pub(in crate::kernel) fn wrap_path_context_with_introductions(
    proposition: Proposition,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> (Proposition, LoweringIntroductions) {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    // Certified outputs (including read equations and population bounds) are
    // consequences of evaluation, not conditions selecting its path. Keep
    // them in the fact stream, but never turn them into additional hypotheses.
    // Uncertified branch facts and outstanding obligations still guard the goal.
    let retained = || {
        facts.fact_iter().filter(|fact| {
            !fact.is_certified()
                && !fact.is_logical_read_equation()
                && !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition())
        })
    };

    let introductions = retained()
        .map(|_| LoweringIntroduction::PathFactGuard)
        .chain(
            obligations
                .iter()
                .map(|_| LoweringIntroduction::ObligationGuard),
        )
        .collect();

    let proposition = retained().rev().fold(proposition, |body, fact| {
        Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
    });

    (proposition, introductions)
}

pub(in crate::kernel) fn public_execution_pure_facts(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> ExecutionFacts {
    facts.persistent_facts().filtered(|fact| fact.is_public())
}

pub(in crate::kernel) fn memory_effect_execution_facts(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> ExecutionFacts {
    // Internal memory effects and their theorem-backed derivations must
    // survive the public-fact projection. The latter is planning metadata,
    // not an additional path premise, and is consumed when Click constructs
    // the corresponding explicit transport step.
    facts.persistent_facts().filtered(|fact| {
        fact.transport_theorem().is_some()
            || fact.reference_observation.is_some()
            || matches!(
                fact.proposition(),
                Proposition::MemoryMutatesOnly { .. }
                    | Proposition::MemoryEffectSummary { .. }
                    | Proposition::HeapAllocationFreed { .. }
            )
    })
}

pub(crate) fn solve_builtin_prop(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            algebraic_terms_equal(left.native_compat(), right.native_compat())
        }
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => left == right,
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            sequence_terms_equal_by_elements(left, right)
        }
        Proposition::SequenceMembership { .. } => {
            crate::kernel::spec::checks_retained_sequence_comparison(
                proposition,
                true,
                |condition, truth| {
                    solve_builtin_prop(&Proposition::condition_is(condition.clone(), truth))
                },
            ) == Some(true)
        }
        Proposition::Equal(left, right) => left == right,
        Proposition::ConditionIs(condition, expected)
            if let Some(actual) = condition.operand_view().closed_float_predicate_value() =>
        {
            actual == *expected
        }
        condition_source_0 @ Proposition::ConditionIs(_, expected)
            if let Some((ConditionTerm::Constant(actual), _)) =
                condition_source_0.condition_native() =>
        {
            actual == expected
        }
        Proposition::ConditionIs(condition, expected) => {
            crate::kernel::machine_integer::comparison::closed_condition_value(
                condition.native_compat(),
            )
            .or_else(|| {
                crate::kernel::proof::integer_arithmetic::literal_integer_comparison_value(
                    condition.native_compat(),
                )
            })
            .is_some_and(|actual| actual == *expected)
        }
        Proposition::And(left, right) => solve_builtin_prop(left) && solve_builtin_prop(right),
        Proposition::Or(left, right) => solve_builtin_prop(left) || solve_builtin_prop(right),
        Proposition::Not(body) => {
            disprove_builtin_prop(body) || conjunction_order_facts_are_inconsistent(body)
        }
        // A guarded proposition is true wherever its guard has no model, and
        // a universal over one is true for the arbitrary binder. Only the
        // unsatisfiable-guard case is decided here; a guard that may hold
        // keeps its consequent as an ordinary obligation.
        Proposition::Implies(antecedent, _) => conjunction_order_facts_are_inconsistent(antecedent),
        Proposition::ForAll { body, .. } => {
            matches!(body.as_ref(), Proposition::Implies(antecedent, _)
                if conjunction_order_facts_are_inconsistent(antecedent))
        }
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } => bytes.as_const().is_some_and(|bytes| {
            let written = crate::kernel::eval::pointer_read_over_immediate_store(base);
            memory.access_in_bounds(written.as_ref().unwrap_or(base), bytes)
        }),
        Proposition::ResourceSeparate { .. } | Proposition::ResourceContains { .. } => false,
        Proposition::MemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => memory.access_in_bounds(pointer, *byte_width),
        _ => false,
    }
}

/// A conjunction of signed order facts with no model, such as the guard
/// `t <= k and k < t` of a universal whose range is empty at a loop entry.
/// The check reads only the conjunction's own order facts. A cycle through
/// constants only (`0 <= k and k < 0`) is deliberately not decided here:
/// constant ranges keep their finite-range treatment, whose `enumerate`
/// certificates written proofs rely on.
pub(in crate::kernel) fn conjunction_order_facts_are_inconsistent(
    proposition: &Proposition,
) -> bool {
    let mut facts = Vec::new();
    super::order_reasoning::collect_order_facts_from_assumed_proposition(proposition, &mut facts);
    facts.len() >= 2 && super::order_reasoning::order_facts_form_strict_cycle(&facts)
}

pub(in crate::kernel) fn disprove_builtin_prop(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::ConditionIs(condition, expected)
            if let Some(actual) = condition.operand_view().closed_float_predicate_value() =>
        {
            actual != *expected
        }
        condition_source_0 @ Proposition::ConditionIs(_, expected)
            if let Some((ConditionTerm::Constant(actual), _)) =
                condition_source_0.condition_native() =>
        {
            actual != expected
        }
        Proposition::ConditionIs(condition, expected) => {
            crate::kernel::machine_integer::comparison::closed_condition_value(
                condition.native_compat(),
            )
            .or_else(|| {
                crate::kernel::proof::integer_arithmetic::literal_integer_comparison_value(
                    condition.native_compat(),
                )
            })
            .is_some_and(|actual| actual != *expected)
        }
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            sequence_terms_definitely_distinct(left, right)
        }
        Proposition::SequenceMembership { .. } => {
            crate::kernel::spec::checks_retained_sequence_comparison(
                proposition,
                false,
                |condition, truth| {
                    solve_builtin_prop(&Proposition::condition_is(condition.clone(), truth))
                },
            ) == Some(true)
        }
        Proposition::Equal(Term::ProgramValue(left), Term::ProgramValue(right)) => {
            program_values_definitely_distinct(left.native_compat(), right.native_compat())
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            algebraic_terms_definitely_distinct(left.native_compat(), right.native_compat())
        }
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => left != right,
        // A null pointer has no provenance, so it shares no allocation.
        Proposition::Predicate { .. }
            if let Some((left, right)) =
                crate::kernel::assumptions::same_allocation_pointers(proposition) =>
        {
            left.is_null() || right.is_null()
        }
        Proposition::And(left, right) => {
            disprove_builtin_prop(left) || disprove_builtin_prop(right)
        }
        Proposition::Or(left, right) => disprove_builtin_prop(left) && disprove_builtin_prop(right),
        Proposition::Not(body) => solve_builtin_prop(body),
        _ => false,
    }
}

fn algebraic_terms_equal(left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
    if !left.is_well_formed()
        || !right.is_well_formed()
        || left.algebraic_type != right.algebraic_type
    {
        return false;
    }
    // Reflexivity applies to opaque applications and symbolic matches too.
    // This checks exact terms, not injectivity or evaluation of pure calls.
    left.node == right.node
        || algebraic_match_rebuilds_scrutinee(left, right)
        || algebraic_match_rebuilds_scrutinee(right, left)
        || match (&left.node, &right.node) {
            (
                AlgebraicTermNode::PureFunctionApplication {
                    name: an,
                    arguments: aa,
                },
                AlgebraicTermNode::PureFunctionApplication {
                    name: bn,
                    arguments: ba,
                },
            ) if an == bn => {
                crate::kernel::SharedPureApplication::intern(an.clone(), aa.clone())
                    == crate::kernel::SharedPureApplication::intern(bn.clone(), ba.clone())
            }
            _ => false,
        }
}

/// Check the arm bodies and binders of a reconstruction. Callers validate
/// the operand types and schemas before using this as equality evidence.
pub(in crate::kernel) fn algebraic_match_rebuilds_scrutinee(
    matched: &AlgebraicTerm,
    other: &AlgebraicTerm,
) -> bool {
    let AlgebraicTermNode::Match { scrutinee, arms } = &matched.node else {
        return false;
    };
    scrutinee.as_ref() == other
        && arms.iter().all(|arm| {
            let AlgebraicTermNode::Constructor { variant, fields } = &arm.body.node else {
                return false;
            };
            crate::instrumentation::record_deterministic_work(arm.bindings.len() + 1);
            if variant != &arm.variant || fields != &arm.bindings {
                return false;
            }
            let mut variables = std::collections::HashSet::with_capacity(arm.bindings.len());
            arm.bindings.iter().all(|binding| {
                let variable = match binding {
                    AlgebraicValue::Program(
                        ProgramValue::Int128(MachineTerm::Variable(variable))
                        | ProgramValue::UInt128(MachineTerm::Variable(variable)),
                    ) => Some(*variable),
                    _ => crate::kernel::proof::term_rewrite::typed_declaration_variable(binding)
                        .map(|(_, variable)| variable),
                };
                variable.is_some_and(|variable| variables.insert(variable))
            })
        })
}

#[cfg(test)]
#[path = "../../scaling_tests/kernel/reasoning/path_facts/algebraic_reconstruction.rs"]
mod algebraic_reconstruction_scaling_tests;

fn algebraic_terms_definitely_distinct(left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
    if !left.is_well_formed() || !right.is_well_formed() {
        return false;
    }
    if left.algebraic_type != right.algebraic_type {
        return true;
    }
    match (&left.node, &right.node) {
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
            left_variant != right_variant
                || left_fields.len() != right_fields.len()
                || left_fields
                    .iter()
                    .zip(right_fields)
                    .any(|(left, right)| match (left, right) {
                        (AlgebraicValue::Program(left), AlgebraicValue::Program(right)) => {
                            program_values_definitely_distinct(left, right)
                        }
                        (AlgebraicValue::Algebraic(left), AlgebraicValue::Algebraic(right)) => {
                            algebraic_terms_definitely_distinct(left, right)
                        }
                        _ => true,
                    })
        }
        _ => false,
    }
}

fn sequence_terms_equal_by_elements(left: &SequenceTerm, right: &SequenceTerm) -> bool {
    if let (Some(left_type), Some(right_type)) = (left.element_type, right.element_type)
        && left_type != right_type
    {
        return false;
    }
    let mut left = crate::kernel::spec::sequence_elements(left);
    let mut right = crate::kernel::spec::sequence_elements(right);
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) if left == right => {}
            (None, None) => return true,
            _ => return false,
        }
    }
}

fn sequence_terms_definitely_distinct(left: &SequenceTerm, right: &SequenceTerm) -> bool {
    if let (Some(left_type), Some(right_type)) = (left.element_type, right.element_type)
        && left_type != right_type
    {
        return true;
    }
    let mut left = crate::kernel::spec::sequence_elements(left);
    let mut right = crate::kernel::spec::sequence_elements(right);
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) if program_values_definitely_distinct(left, right) => {
                return true;
            }
            (Some(_), Some(_)) => {}
            (None, None) => return false,
            _ => return true,
        }
    }
}

pub(in crate::kernel) fn program_values_definitely_distinct(
    left: &ProgramValue,
    right: &ProgramValue,
) -> bool {
    fn constant(bits: &MachineTerm) -> Option<u64> {
        match bits {
            bits32_constant!(value) => Some(u64::from(constant_u32(*value))),
            int64_constant!(value) => Some(constant_i64(*value) as u64),
            uint64_constant!(value) => Some(constant_u64(*value)),
            _ => None,
        }
    }

    match (left, right) {
        (ProgramValue::Int8(left), ProgramValue::Int8(right)) => {
            matches!((constant(left), constant(right)), (Some(left), Some(right)) if left != right)
        }
        (ProgramValue::Int16(left), ProgramValue::Int16(right))
        | (ProgramValue::Int32(left), ProgramValue::Int32(right))
        | (ProgramValue::UInt8(left), ProgramValue::UInt8(right))
        | (ProgramValue::UInt16(left), ProgramValue::UInt16(right))
        | (ProgramValue::UInt32(left), ProgramValue::UInt32(right))
        | (ProgramValue::Int64(left), ProgramValue::Int64(right))
        | (ProgramValue::UInt64(left), ProgramValue::UInt64(right)) => {
            matches!((constant(left), constant(right)), (Some(left), Some(right)) if left != right)
        }
        _ => false,
    }
}

/// The element index a byte offset names, *modulo `2^32`*.
///
/// A residue is enough for a disequality and for an exclusion; a caller that
/// reads the answer as a number wants [`exact_element_delta_from_offset`].
/// Either way the answer has to be a residue of the delta, and an
/// `Int64Scaled` one is not: it scales its *64-bit* value, so the 32-bit term
/// holding that value denotes the index only when the value happens to fit
/// `int32`, and `unsigned int k; a[k]` reaches here as
/// `UInt64From32(k)` — a term of a different width from the one every
/// consumer compares it against. This is the arm
/// [`exact_element_delta_from_offset`] already refused, for the same reason,
/// and it is refused here too rather than carried: a width threaded alongside
/// the index would have to be got right independently at each of the dozen
/// consumers and at every certificate that re-checks them, while refusing
/// costs an answer none of them can use.
pub(in crate::kernel) fn element_index_from_offset(
    offset: &AddressOffset,
    element_width: u32,
) -> Option<MachineTerm> {
    if let AddressOffset::Constant(bytes) = offset {
        return element_index_literal(*bytes, element_width).map(MachineTerm::constant);
    }
    shared_element_index_from_offset(offset, element_width)
        .map(|index| index.structural_value().clone())
}

/// The same residue extraction retaining shared index operands. Native-output
/// callers keep `element_index_from_offset`; evidence checking uses this view.
pub(in crate::kernel) fn shared_element_index_from_offset(
    offset: &AddressOffset,
    element_width: u32,
) -> Option<crate::kernel::SharedMachineIntegerTerm> {
    use crate::kernel::{
        KernelTerm, MachineBinaryOp as B, MachineIntegerType as T, SharedMachineIntegerTerm as S,
    };
    if element_width == 0 {
        return None;
    }
    let constant = |n: u32| S::intern(T::Int32, MachineTerm::constant(n));
    let root = |v: &S| KernelTerm::retained_machine_operand(T::Int32, v.operand_view());
    match offset {
        AddressOffset::Add(a, b) => {
            if a.as_ref() == &AddressOffset::Constant(0) {
                return shared_element_index_from_offset(b, element_width);
            }
            if b.as_ref() == &AddressOffset::Constant(0) {
                return shared_element_index_from_offset(a, element_width);
            }
            let a = shared_element_index_from_offset(a, element_width)?;
            let b = shared_element_index_from_offset(b, element_width)?;
            S::from_shared(
                T::Int32,
                crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
                    T::Int32,
                    B::Add,
                    root(&a),
                    root(&b),
                ),
            )
        }
        AddressOffset::Int32Scaled { value, byte_width }
            if *byte_width == i64::from(element_width) =>
        {
            Some(value.clone())
        }
        AddressOffset::Int32Scaled { value, byte_width } if element_width == 1 => {
            let width = u32::try_from(*byte_width).ok()?;
            match width {
                0 => Some(constant(0)),
                1 => Some(value.clone()),
                _ => S::from_shared(
                    T::Int32,
                    KernelTerm::machine_binary_shared(
                        T::Int32,
                        B::Multiply,
                        [root(value), root(&constant(width))],
                    ),
                ),
            }
        }
        AddressOffset::Constant(bytes) => {
            element_index_literal(*bytes, element_width).map(constant)
        }
        _ => None,
    }
}

/// [`element_index_from_offset`] for a caller holding facts, which is the one
/// thing that turns a 64-bit index into a 32-bit one.
///
/// An `Int64Scaled` displacement scales its *64-bit* value, so the term
/// holding that value names an element index only where full-width evidence
/// places it in the signed word range. Exact constants work for either sign;
/// unsigned symbolic values require their native upper bound. Checked scalar
/// aliases preserve that bound, including a constant subtraction whose bound
/// the proof establishes explicitly. No low-word fact establishes high bits.
#[cfg(test)]
pub(in crate::kernel) fn element_index_from_offset_with_facts(
    offset: &AddressOffset,
    element_width: u32,
    assumptions: &PureFactContext,
) -> Option<MachineTerm> {
    if let AddressOffset::Constant(bytes) = offset {
        return element_index_literal(*bytes, element_width).map(MachineTerm::constant);
    }
    shared_element_index_from_offset_with_facts(offset, element_width, assumptions)
        .map(|index| index.structural_value().clone())
}

pub(in crate::kernel) fn shared_element_index_from_offset_with_facts(
    offset: &AddressOffset,
    element_width: u32,
    assumptions: &PureFactContext,
) -> Option<crate::kernel::SharedMachineIntegerTerm> {
    use crate::kernel::{MachineIntegerType as T, MachineOperandView as V};
    let low_word = |v: V<'_>| {
        let root = crate::kernel::KernelTerm::retained_machine_operand(T::UInt64, v)
            .checking_legacy_machine_conversion(T::UInt64, T::UInt32);
        V::Shared(&root).retain(T::Int32)
    };
    if element_width == 0 {
        return None;
    }
    if let Some(index) = shared_element_index_from_offset(offset, element_width) {
        return Some(index);
    }
    match offset {
        AddressOffset::Add(left, right) => Some(shared_offset_sum(
            shared_element_index_from_offset_with_facts(left, element_width, assumptions)?,
            shared_element_index_from_offset_with_facts(right, element_width, assumptions)?,
        )),
        AddressOffset::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } if *byte_width == i64::from(element_width) => {
            // The value is sixty-four bits wide, so only a sixty-four-bit
            // fact pins it: a thirty-two-bit one names the low word and
            // leaves the rest, and `exact_signed_constant` accepts those.
            // `unsigned` is part of the question rather than a check after
            // it, because the two readings of one word are different numbers.
            if let Some(index) = crate::kernel::assumptions::exact_sixty_four_bit_constant_view(
                value.operand_view(),
                *unsigned,
                assumptions,
            ) {
                return i32::try_from(index)
                    .ok()
                    .map(|index| V::Legacy(&MachineTerm::constant(index as u32)).retain(T::Int32));
            }
            if !*unsigned {
                // A signed index in `0..=INT_MAX` is its own low word.
                return assumptions
                    .int64_index_fits_int32_view(value.operand_view())
                    .then(|| low_word(value.operand_view()));
            }
            let bounded = |candidate: V<'_>| assumptions.uint64_index_fits_int32_view(candidate);
            if bounded(value.operand_view()) {
                return Some(low_word(value.operand_view()));
            }
            // Modular calls can name an unchanged native index through a
            // checked scalar-result equality. Transport the bound through
            // that full-width equality, never through equality of low words.
            for (alias, fact) in assumptions.exact_uint64_equalities_view(value.operand_view()) {
                crate::instrumentation::record_deterministic_work(1);
                if bounded(V::Legacy(alias)) {
                    crate::kernel::assumptions::record_implicit_consulted_premises(
                        assumptions,
                        &Proposition::condition_is(fact.clone(), true),
                    );
                    return Some(low_word(V::Legacy(alias)));
                }
            }
            // A constant subtraction retains equality of the full-width
            // operands. Its bound must still be proved explicitly; this does
            // not infer nonemptiness or arithmetic ranges from a low word.
            if let Some((T::UInt64, MachineBinaryOp::Subtract, [left, right])) =
                value.operand_view().binary()
                && right.uint64_constant().is_some()
            {
                for (alias, fact) in assumptions.exact_uint64_equalities_view(left) {
                    crate::instrumentation::record_deterministic_work(1);
                    let candidate =
                        crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
                            T::UInt64,
                            MachineBinaryOp::Subtract,
                            crate::kernel::KernelTerm::retained_machine_operand(
                                T::UInt64,
                                V::Legacy(alias),
                            ),
                            crate::kernel::KernelTerm::retained_machine_operand(T::UInt64, right),
                        );
                    if bounded(V::Shared(&candidate)) {
                        crate::kernel::assumptions::record_implicit_consulted_premises(
                            assumptions,
                            &Proposition::condition_is(fact.clone(), true),
                        );
                        return Some(low_word(V::Shared(&candidate)));
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// An element delta split so that it is *exact*: the true delta in `i64` is
/// `sext(index) + constant`.
///
/// [`element_index_from_offset`] answers with one `MachineTerm`, and that
/// is a lossy answer for anything but an equality. A byte offset is
/// mathematical `i64` — [`AddressOffset::scale_int32`] sign-extends its
/// index before scaling, and `Add` adds exactly — while a `MachineTerm` is
/// modular, so collapsing a sum of offsets into [`MachineTerm::add`] keeps
/// the delta only *modulo* `2^32`. A membership or order conclusion drawn from
/// such a term would be reading a residue as a number.
///
/// Keeping the constant part in `i64` beside the index loses nothing and wraps
/// nothing: every constant byte displacement a struct field or a fixed array
/// subscript contributes lands here, exactly, and only a *second* symbolic
/// index would need an add this cannot do.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct ExactElementDelta {
    /// The one symbolic element index in the delta, or `Constant(0)` when the
    /// delta is wholly constant. Its *signed* value is part of the delta.
    pub(in crate::kernel) index: SharedMachineIntegerTerm,
    /// The exact constant part, in elements. Not reduced to `i32`: a delta far
    /// outside `i32` is still an exact delta, and refusing it here would be a
    /// silent truncation.
    pub(in crate::kernel) constant: i64,
}

impl ExactElementDelta {
    /// The delta of a wholly constant number of elements.
    fn constant(constant: i64) -> Self {
        Self {
            index: MachineOperandView::Legacy(&MachineTerm::constant(0))
                .retain(MachineIntegerType::Int32),
            constant,
        }
    }

    /// The zero delta: a pointer at its base.
    pub(in crate::kernel) fn zero() -> Self {
        Self::constant(0)
    }

    /// This delta as one retained int32 term whose *signed* value is the delta,
    /// for a caller that states it as an ordinary index bound. `None` when the
    /// two parts cannot be joined without a modular add, which a symbolic index
    /// beside a nonzero constant cannot.
    pub(in crate::kernel) fn as_index_term(&self) -> Option<SharedMachineIntegerTerm> {
        if self.constant == 0 {
            return Some(self.index.clone());
        }
        if !self.is_constant() {
            return None;
        }
        i32::try_from(self.constant).ok().map(|constant| {
            MachineOperandView::Legacy(&MachineTerm::constant(constant as u32))
                .retain(MachineIntegerType::Int32)
        })
    }

    /// Whether this delta names no symbolic index, so its `i64` value is the
    /// whole of it.
    pub(in crate::kernel) fn is_constant(&self) -> bool {
        self.index.operand_view().word32_constant() == Some(0)
    }

    /// The two deltas added, when at most one of them is symbolic. Two
    /// symbolic indices would need a modular add, which is the loss this type
    /// exists to avoid.
    fn add(self, other: Self) -> Option<Self> {
        let index = match (self.is_constant(), other.is_constant()) {
            (_, true) => self.index,
            (true, false) => other.index,
            (false, false) => return None,
        };
        Some(Self {
            index,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    /// `self - other`, when the subtraction stays exact: either the subtrahend
    /// is constant, or the two symbolic indices cancel.
    ///
    /// Two indices cancel only when their difference is the true one and not a
    /// residue — `4 * i + 3` is three elements above `i + i + i + i` only while
    /// the scaling does not wrap — so the cancellation goes through the same
    /// [`crate::kernel::assumptions::exact_affine_index_difference_views`] every other
    /// membership conclusion uses, and answers `None` without the premise it
    /// needs.
    pub(in crate::kernel) fn subtract(
        self,
        other: Self,
        assumptions: Option<&PureFactContext>,
    ) -> Option<Self> {
        let constant = self.constant.checked_sub(other.constant)?;
        if other.is_constant() {
            return Some(Self {
                index: self.index,
                constant,
            });
        }
        if let Some(difference) = crate::kernel::assumptions::exact_affine_index_difference_views(
            self.index.operand_view(),
            other.index.operand_view(),
            assumptions,
        ) {
            return difference.checked_add(constant).map(Self::constant);
        }
        // Two indices with no constant difference between them. Their modular
        // difference still names the delta while neither is negative, since
        // `sext(a) - sext(b)` then lies in `(-2^31, 2^31)` and the 32-bit
        // subtraction is the subtraction. That is the premise a range restated
        // in another base's coordinates as `b - a` needs, and without it the
        // restated start and the real delta can sit `2^32` elements apart.
        (crate::kernel::assumptions::element_index_is_nonnegative_view(
            self.index.operand_view(),
            assumptions,
        ) && crate::kernel::assumptions::element_index_is_nonnegative_view(
            other.index.operand_view(),
            assumptions,
        ))
        .then(|| Self {
            index: crate::kernel::assumptions::index_binary(
                MachineBinaryOp::Subtract,
                self.index.operand_view(),
                other.index.operand_view(),
            ),
            constant,
        })
    }
}

/// [`element_index_from_offset`] for a caller that needs the delta's value and
/// not merely its residue. See [`ExactElementDelta`].
pub(in crate::kernel) fn exact_element_delta_from_offset(
    offset: &AddressOffset,
    element_width: u32,
) -> Option<ExactElementDelta> {
    if element_width == 0 {
        return None;
    }
    match offset {
        AddressOffset::Add(left, right) => exact_element_delta_from_offset(left, element_width)?
            .add(exact_element_delta_from_offset(right, element_width)?),
        AddressOffset::Int32Scaled { value, byte_width }
            if *byte_width == i64::from(element_width) =>
        {
            Some(ExactElementDelta {
                index: value.clone(),
                constant: 0,
            })
        }
        AddressOffset::Constant(offset) if offset % i64::from(element_width) == 0 => Some(
            ExactElementDelta::constant(offset / i64::from(element_width)),
        ),
        // An `Int64Scaled` index scales its *64-bit* value, which is not the
        // signed value of the 32-bit term holding it, so the term cannot stand
        // for the delta. A constant one has already been folded into
        // `Constant` by `scale_int64`.
        AddressOffset::Constant(_)
        | AddressOffset::Variable(_)
        | AddressOffset::Int32Scaled { .. }
        | AddressOffset::Int64Scaled { .. } => None,
    }
}

pub(in crate::kernel) fn common_pointer_offset_element_width(
    left: &AddressOffset,
    right: &AddressOffset,
) -> Option<u32> {
    fn offset_element_width(offset: &AddressOffset) -> Option<u32> {
        match offset {
            AddressOffset::Int32Scaled { byte_width, .. }
            | AddressOffset::Int64Scaled { byte_width, .. } => {
                u32::try_from(*byte_width).ok().filter(|width| *width > 0)
            }
            AddressOffset::Add(left, right) => {
                match (offset_element_width(left), offset_element_width(right)) {
                    (Some(left), Some(right)) if left == right => Some(left),
                    (Some(width), None) | (None, Some(width)) => Some(width),
                    (None, None) => None,
                    _ => None,
                }
            }
            AddressOffset::Constant(_) | AddressOffset::Variable(_) => None,
        }
    }

    match (offset_element_width(left), offset_element_width(right)) {
        (Some(left), Some(right)) if left == right => Some(left),
        (Some(width), None) | (None, Some(width)) => Some(width),
        _ => None,
    }
}

pub(in crate::kernel) fn shared_pointer_byte_offset_from_base(
    pointer: &Address,
    base: &Address,
) -> Option<SharedMachineIntegerTerm> {
    if pointer.base != base.base {
        return None;
    }
    if pointer.offset == base.offset {
        return Some(
            MachineOperandView::Legacy(&MachineTerm::constant(0)).retain(MachineIntegerType::Int32),
        );
    }
    if base.offset == AddressOffset::Constant(0) {
        return shared_byte_offset_from_pointer_offset(&pointer.offset);
    }

    // Pointer arithmetic is represented as a binary tree. A field access
    // after an indexed access therefore has the shape
    // `((base + stride) + field)`, rather than a single addition whose left
    // child is exactly `base`. Walk the additive tree so the common base is
    // cancelled before constructing the byte offset; this keeps resource
    // checks independent of harmless grouping differences in pointer
    // arithmetic.
    fn offset_from_nested_base(
        offset: &AddressOffset,
        base: &AddressOffset,
    ) -> Option<SharedMachineIntegerTerm> {
        if offset == base {
            return Some(
                MachineOperandView::Legacy(&MachineTerm::constant(0))
                    .retain(MachineIntegerType::Int32),
            );
        }
        let AddressOffset::Add(left, right) = offset else {
            return None;
        };
        if left.as_ref() == base {
            return shared_byte_offset_from_pointer_offset(right);
        }
        if right.as_ref() == base {
            return shared_byte_offset_from_pointer_offset(left);
        }
        if let Some(left_offset) = offset_from_nested_base(left, base) {
            return Some(shared_offset_sum(
                left_offset,
                shared_byte_offset_from_pointer_offset(right)?,
            ));
        }
        if let Some(right_offset) = offset_from_nested_base(right, base) {
            return Some(shared_offset_sum(
                shared_byte_offset_from_pointer_offset(left)?,
                right_offset,
            ));
        }
        None
    }

    offset_from_nested_base(&pointer.offset, &base.offset).or_else(|| {
        let pointer_offset = shared_byte_offset_from_pointer_offset(&pointer.offset)?;
        let base_offset = shared_byte_offset_from_pointer_offset(&base.offset)?;
        Some(crate::kernel::assumptions::index_binary(
            MachineBinaryOp::Subtract,
            pointer_offset.operand_view(),
            base_offset.operand_view(),
        ))
    })
}

// Native output boundaries need no arena round trip for a literal. Share its
// width/range rule with the retained builder, while retaining compound indices.
fn element_index_literal(bytes: i64, width: u32) -> Option<u32> {
    if width == 0 || bytes % i64::from(width) != 0 {
        return None;
    }
    i32::try_from(bytes / i64::from(width))
        .ok()
        .map(|index| index as u32)
}

pub(in crate::kernel) fn byte_offset_from_pointer_offset(
    offset: &AddressOffset,
) -> Option<MachineTerm> {
    if let AddressOffset::Constant(bytes) = offset {
        return element_index_literal(*bytes, 1).map(MachineTerm::constant);
    }
    shared_byte_offset_from_pointer_offset(offset).map(|index| index.structural_value().clone())
}

fn shared_offset_sum(
    a: crate::kernel::SharedMachineIntegerTerm,
    b: crate::kernel::SharedMachineIntegerTerm,
) -> crate::kernel::SharedMachineIntegerTerm {
    use crate::kernel::{KernelTerm, MachineIntegerType as T, MachineOperandView as V};
    let root = crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
        T::Int32,
        MachineBinaryOp::Add,
        KernelTerm::retained_machine_operand(T::Int32, a.operand_view()),
        KernelTerm::retained_machine_operand(T::Int32, b.operand_view()),
    );
    V::Shared(&root).retain(T::Int32)
}

pub(in crate::kernel) fn shared_byte_offset_from_pointer_offset(
    offset: &AddressOffset,
) -> Option<crate::kernel::SharedMachineIntegerTerm> {
    use crate::kernel::{KernelTerm, MachineIntegerType as T, MachineOperandView as V};
    let constant = |n| V::Legacy(&MachineTerm::constant(n)).retain(T::Int32);
    match offset {
        AddressOffset::Constant(offset) => (i32::MIN as i64..=i32::MAX as i64)
            .contains(offset)
            .then_some(constant((*offset as i32) as u32)),
        AddressOffset::Add(left, right) => Some(shared_offset_sum(
            shared_byte_offset_from_pointer_offset(left)?,
            shared_byte_offset_from_pointer_offset(right)?,
        )),
        AddressOffset::Int32Scaled { value, byte_width } => {
            let width = u32::try_from(*byte_width).ok()?;
            match width {
                0 => Some(constant(0)),
                1 => Some(value.clone()),
                _ => Some(
                    V::Shared(&KernelTerm::machine_binary_shared(
                        T::Int32,
                        MachineBinaryOp::Multiply,
                        [
                            KernelTerm::retained_machine_operand(T::Int32, value.operand_view()),
                            KernelTerm::retained_machine_operand(
                                T::Int32,
                                constant(width).operand_view(),
                            ),
                        ],
                    ))
                    .retain(T::Int32),
                ),
            }
        }
        AddressOffset::Int64Scaled { byte_width: 0, .. } => Some(constant(0)),
        // A 64-bit index is not a 32-bit byte residue, even when its stride
        // is one. Callers that need its numeric value must use a 64-bit bound.
        AddressOffset::Int64Scaled { .. } | AddressOffset::Variable(_) => None,
    }
}

pub(in crate::kernel) fn element_count_from_bytes(
    bytes: &MachineTerm,
    element_width: u32,
) -> Option<MachineTerm> {
    if element_width == 0 {
        return None;
    }
    if element_width == 1 {
        return Some(bytes.clone());
    }
    let element_width = MachineTerm::constant(element_width);
    match bytes {
        binary_term!(Int32, Multiply, left, right) if right.as_ref() == &element_width => {
            Some(left.as_ref().clone())
        }
        binary_term!(Int32, Multiply, left, right) if left.as_ref() == &element_width => {
            Some(right.as_ref().clone())
        }
        bits32_constant!(bytes)
            if constant_u32(*bytes).is_multiple_of(element_width.as_const()?) =>
        {
            Some(MachineTerm::constant(
                constant_u32(*bytes) / element_width.as_const()?,
            ))
        }
        _ => None,
    }
}

/// The element count of a 64-bit (`uint64`) byte count: `n` of `n * w` at
/// `uint64`, or a `uint64` constant divisible by `w`.
///
/// Reading `n * w` as `n` elements needs the product not to have wrapped. A
/// heap block's `uint64` size is admitted only once `n <= PTRDIFF_MAX / w`
/// is decided for each constant factor `w` of a top-level product
/// (`allocation_size_validity_refusal` in `eval/statements.rs`), so this is
/// for such sizes only, never for an arbitrary `uint64` term.
pub(in crate::kernel) fn uint64_element_count_from_bytes(
    bytes: &MachineTerm,
    element_width: u32,
) -> Option<MachineTerm> {
    if element_width == 0 {
        return None;
    }
    if element_width == 1 {
        return Some(bytes.clone());
    }
    let width = MachineTerm::uint64_constant(u64::from(element_width));
    match bytes {
        binary_term!(UInt64, Multiply, left, right) if right.as_ref() == &width => {
            Some(left.as_ref().clone())
        }
        binary_term!(UInt64, Multiply, left, right) if left.as_ref() == &width => {
            Some(right.as_ref().clone())
        }
        _ => {
            let bytes = bytes.uint64_as_const()?;
            bytes
                .is_multiple_of(u64::from(element_width))
                .then(|| MachineTerm::uint64_constant(bytes / u64::from(element_width)))
        }
    }
}

/// An admitted 64-bit allocation size and a byte count `bytes` in the size's
/// elements: `(n, ceil(bytes / k))` for `n * k` with a constant `k`, else
/// `(size, bytes)`. Then `bytes <= size` iff `ceil(bytes / k) <= n`, and
/// `size < bytes` iff `n < ceil(bytes / k)`.
///
/// Like [`uint64_element_count_from_bytes`], this is exact only for a heap
/// size admitted with `n <= PTRDIFF_MAX / k` decided
/// (`uint64_allocation_size_bytes_are_exact` in `eval/statements.rs`), so that
/// `n * k` did not wrap; never for an arbitrary `uint64` term.
pub(in crate::kernel) fn uint64_size_in_elements(
    size: &MachineTerm,
    bytes: u64,
) -> (&MachineTerm, MachineTerm) {
    if let binary_term!(UInt64, Multiply, left, right) = size {
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (_, Some(width)) if width > 0 => {
                return (left, MachineTerm::uint64_constant(bytes.div_ceil(width)));
            }
            (Some(width), _) if width > 0 => {
                return (right, MachineTerm::uint64_constant(bytes.div_ceil(width)));
            }
            _ => {}
        }
    }
    (size, MachineTerm::uint64_constant(bytes))
}

/// A byte offset `index * stride + field` into an array of `stride`-byte
/// elements, as a struct array element's field address is formed: a scaled
/// index, plus a constant. A signed 64-bit `index` (`signed`) is C's
/// `ptrdiff_t` reading of the index, an unsigned one its `size_t` value.
#[derive(Clone, Debug)]
pub(in crate::kernel) struct ScaledElementOffset {
    pub(in crate::kernel) index: crate::kernel::SharedMachineIntegerTerm,
    pub(in crate::kernel) signed: bool,
    pub(in crate::kernel) stride: i64,
    pub(in crate::kernel) field: i64,
}

/// The [`ScaledElementOffset`] an offset spells: `i` scaled by `w`
/// (`Int32Scaled`, sign extended, or `Int64Scaled`), or a byte displacement
/// `(int64)i * w` (an `Int64Scaled` of width one whose value is the `int64`
/// product with a positive constant, the front end's spelling of `&p[i]` for
/// a struct `p`), plus at most one constant. The product is read as `i`
/// elements: a caller's bound `0 <= i <= n` with `n <= PTRDIFF_MAX / w`
/// rules out its overflow.
pub(in crate::kernel) fn scaled_element_offset(
    offset: &AddressOffset,
) -> Option<ScaledElementOffset> {
    let (scaled, field) = match offset {
        AddressOffset::Add(left, right) => match (left.as_ref(), right.as_ref()) {
            (scaled, AddressOffset::Constant(field)) | (AddressOffset::Constant(field), scaled) => {
                (scaled, *field)
            }
            _ => return None,
        },
        scaled => (scaled, 0),
    };
    use crate::kernel::{
        KernelTerm, MachineBinaryOp, MachineIntegerType as Ty, SharedMachineIntegerTerm,
    };
    let (index, signed, stride) = match scaled {
        AddressOffset::Int32Scaled { value, byte_width } => {
            let root = KernelTerm::retained_machine_operand(Ty::Int32, value.operand_view());
            let wide = root.checking_legacy_machine_conversion(Ty::Int32, Ty::Int64);
            (
                SharedMachineIntegerTerm::from_shared(Ty::Int64, wide)?,
                true,
                *byte_width,
            )
        }
        AddressOffset::Int64Scaled {
            value,
            byte_width: 1,
            unsigned: false,
        } => match value.operand_view().binary() {
            Some((Ty::Int64, MachineBinaryOp::Multiply, [left, right])) => {
                match (left.int64_constant(), right.int64_constant()) {
                    (None, Some(stride)) => (left.retain(Ty::Int64), true, stride),
                    (Some(stride), None) => (right.retain(Ty::Int64), true, stride),
                    _ => (value.clone(), true, 1),
                }
            }
            _ => (value.clone(), true, 1),
        },
        AddressOffset::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => (value.clone(), !unsigned, *byte_width),
        _ => return None,
    };
    (stride > 0).then_some(ScaledElementOffset {
        index,
        signed,
        stride,
        field,
    })
}

/// The conditions that place an element index at most `count`, or below it
/// when `strict`, for a `count` at most `PTRDIFF_MAX`: `index <= count` at
/// `uint64` for an unsigned index; for a signed one, the same unsigned
/// comparison of its bits when the facts decide it, since for such a
/// `count`, `0 <= index <= count` signed iff `index <= count` unsigned, and
/// otherwise `0 <= index` and `index <= count` at `int64`. A `size_t` index
/// converted to `ptrdiff_t` keeps its `uint64` facts; a `long` one has
/// signed facts.
pub(in crate::kernel) fn wide_index_bound_conditions(
    index: &crate::kernel::SharedMachineIntegerTerm,
    signed: bool,
    count: &MachineTerm,
    strict: bool,
    assumptions: &PureFactContext,
) -> Vec<ConditionTerm> {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views as compare;
    use crate::kernel::{MachineIntegerType as Ty, MachineOperandView as View};
    let relation = if strict {
        CompareRelation::LessThan
    } else {
        CompareRelation::LessEqual
    };
    let unsigned = compare(
        Ty::UInt64,
        relation,
        [index.operand_view(), View::Legacy(count)],
    );
    if !signed || assumptions.decide(&unsigned) == Some(true) {
        return vec![unsigned];
    }
    let count = MachineTerm::int64_from_uint64_bits(count.clone());
    let zero = MachineTerm::int64_constant(0);
    vec![
        compare(
            Ty::Int64,
            CompareRelation::GreaterEqual,
            [index.operand_view(), View::Legacy(&zero)],
        ),
        compare(
            Ty::Int64,
            relation,
            [index.operand_view(), View::Legacy(&count)],
        ),
    ]
}

pub(in crate::kernel) fn int32_element_count_from_bytes(
    bytes: &MachineTerm,
) -> Option<MachineTerm> {
    element_count_from_bytes(bytes, 4)
}

pub(in crate::kernel) fn add_path_fact(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    proposition: Proposition,
) -> Option<()> {
    add_path_fact_with_visibility(facts, assumptions, proposition, true)
}

pub(in crate::kernel) fn add_path_fact_with_visibility(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    proposition: Proposition,
    public: bool,
) -> Option<()> {
    add_path_fact_with_visibility_after_effect(facts, assumptions, proposition, public, false)
}

fn add_path_fact_with_visibility_after_effect(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    proposition: Proposition,
    public: bool,
    certified_after_effect: bool,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_path_fact_with_visibility(
            facts,
            assumptions,
            condition.native_compat().clone(),
            value,
            public,
            certified_after_effect,
        );
    }

    // Redundant-fact suppression is an exact test only. A general proof that
    // the path fact already follows is proof search inside lowering; keeping
    // the fact instead costs one fact-store entry and keeps the path's public
    // post-state exact.
    if assumptions.proves_exact(&proposition)
        || facts.iter().any(|fact| fact.proposition() == &proposition)
    {
        return Some(());
    }

    facts.push(if public {
        ExecutionPureFact::new(proposition)
    } else {
        ExecutionPureFact::internal(proposition)
    });
    Some(())
}

pub(in crate::kernel) fn add_condition_path_fact(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, true, false)
}

pub(in crate::kernel) fn add_internal_condition_path_fact(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, false, false)
}

/// Adds a condition fact the facts already decide, unless the context holds
/// it exactly. A derived fact is normally dropped, but the equality graph
/// learns only from admitted facts: a no-overflow fact for a byte product
/// (`byte_product_offsets`) has to be admitted for the graph to relate the
/// byte offset to its element offset, even when bounds decide it.
pub(in crate::kernel) fn add_decided_condition_path_fact(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    if assumptions.exact_condition_value(&condition) == Some(value) {
        return Some(());
    }
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, true, true)
}

fn add_condition_path_fact_with_visibility(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
    public: bool,
    certified_after_effect: bool,
) -> Option<()> {
    // A fact certified after a memory effect is part of that transition's
    // public post-state, even when the pre-effect assumptions can derive the
    // same truth value. Dropping it here loses the exact state fact that a
    // later statement (and its surface certificate) may require.
    if let Some(known) = assumptions.exact_condition_value(&condition) {
        if known == value && !certified_after_effect {
            return Some(());
        }
        if known != value && !certified_after_effect {
            return None;
        }
    }
    if let Some(known) = PureFactContext::decide_intrinsically(&condition) {
        return (known == value).then_some(());
    }
    // Only the fast decisions settle a path fact; one they leave open is
    // added (`docs/internals/verification-efficiency.md`).
    let known = assumptions.difference_decision(&condition, &[]);
    if let Some(known) = known {
        if known == value && !certified_after_effect {
            return Some(());
        }
        if known != value && !certified_after_effect {
            return None;
        }
    }

    let opposite = Proposition::condition_is(condition.clone(), !value);
    let proposition = Proposition::condition_is(condition, value);
    if facts.contains_proposition(&proposition) {
        return Some(());
    }
    if facts.contains_proposition(&opposite) {
        return None;
    }
    facts.push(if public {
        ExecutionPureFact::new(proposition)
    } else {
        ExecutionPureFact::internal(proposition)
    });
    Some(())
}

pub(in crate::kernel) fn add_address_offset_equality_execution_pure_facts(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    left: AddressOffset,
    right: AddressOffset,
    value: bool,
) -> Option<()> {
    add_condition_path_fact(
        facts,
        assumptions,
        ConditionTerm::address_offset_equal(left.clone(), right.clone()),
        value,
    )?;

    // A single wide stride is exact, not modular multiplication. Dividing
    // a constant multiple by its nonzero stride gives an equivalent native
    // index comparison in both polarities, without truncating to 32 bits.
    let wide_index_condition = |scaled: &AddressOffset, constant: &AddressOffset| {
        let AddressOffset::Int64Scaled {
            value: index,
            byte_width,
            unsigned,
        } = scaled
        else {
            return None;
        };
        let AddressOffset::Constant(target) = constant else {
            return None;
        };
        if target.checked_rem(*byte_width)? != 0 {
            return None;
        }
        let element = target.checked_div(*byte_width)?;
        let (format, constant) = if *unsigned {
            (
                MachineIntegerType::UInt64,
                MachineTerm::uint64_constant(u64::try_from(element).ok()?),
            )
        } else {
            (
                MachineIntegerType::Int64,
                MachineTerm::int64_constant(element),
            )
        };
        Some(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format,
                crate::kernel::CompareRelation::Equal,
                [
                    index.operand_view(),
                    crate::kernel::MachineOperandView::Legacy(&constant),
                ],
            ),
        )
    };
    if let Some(condition) =
        wide_index_condition(&left, &right).or_else(|| wide_index_condition(&right, &left))
    {
        add_condition_path_fact(facts, assumptions, condition, value)?;
    }

    // The element index a byte offset folds to is that offset divided by the
    // element width, *modulo* `2^32`: every leaf contributes a whole multiple
    // of the width, but `MachineTerm::add` folds the pieces modularly.
    //
    // That makes the two directions different statements. Equal offsets have
    // equal residues, so the affirmative half is arithmetic and needs no
    // premise. Different offsets need not have different residues: `p + i + j`
    // and `p + k` are `2^34` bytes apart at `i == j == i32::MAX`, `k == -2`,
    // and their indices are the same `-2`. Recording `i + j != k` there is
    // recording a false fact, which proves anything.
    //
    // So the disequality is recorded only where each fold is the sum —
    // `rebuilt_offset_is_exact` on the element path, the same premise the
    // opposite polarity of the same question already asks for in
    // `exact_or_unequal`, and exact for the opposite reason: there a residue
    // may refute an offset equality and may not affirm one, while here an
    // offset disequality may not be read off a residue that could have
    // wrapped onto it.
    if let (Some(left_index), Some(right_index)) = (
        shared_element_index_from_offset(&left, 4),
        shared_element_index_from_offset(&right, 4),
    ) && (value
        || assumptions.element_index_rebuild_is_exact(&left)
            && assumptions.element_index_rebuild_is_exact(&right))
    {
        add_condition_path_fact(
            facts,
            assumptions,
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::Equal,
                [left_index.operand_view(), right_index.operand_view()],
            ),
            value,
        )?;
    } else if let Some((index, element)) = single_scaled_index_equal_to_constant(&left, &right)
        .or_else(|| single_scaled_index_equal_to_constant(&right, &left))
    {
        add_condition_path_fact(
            facts,
            assumptions,
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::Equal,
                [
                    index.operand_view(),
                    MachineOperandView::Legacy(&MachineTerm::constant(element as u32)),
                ],
            ),
            value,
        )?;
    }

    Some(())
}

/// `scaled == constant` as the index it selects, when `scaled` is one scaled
/// `int32` index plus constants, `sext(x) * stride + c`: `x * 8 + 4 == 12`
/// holds exactly when `x == 1`. The offset sum is exact, so the equivalence
/// holds in both polarities, at any stride. `None` when the constant is not
/// one of the offsets the index reaches; the offset equality then folds to
/// false (see `pointer_offsets_differ_by_residue`).
pub(in crate::kernel) fn single_scaled_index_equal_to_constant<'term>(
    scaled: &'term AddressOffset,
    constant: &AddressOffset,
) -> Option<(&'term SharedMachineIntegerTerm, i32)> {
    let target = constant.as_const()?;
    let (leaves, offset) = scaled.int32_scaled_linear_form()?;
    let [(index, stride)] = leaves.as_slice() else {
        return None;
    };
    let delta = target.checked_sub(offset)?;
    if *stride == 0 || delta % stride != 0 {
        return None;
    }
    i32::try_from(delta / stride)
        .ok()
        .map(|element| (*index, element))
}

pub(in crate::kernel) fn add_proof_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
) -> Option<()> {
    add_proof_obligation_with_context(obligations, assumptions, proposition, None)
}

pub(in crate::kernel) fn add_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_obligation(
            obligations,
            assumptions,
            condition.native_compat().clone(),
            value,
            context,
        );
    }

    // Obligation suppression keeps two routes: the exact fact index, and the
    // retained atomic memory/resource checkers for a proposition that is
    // already one of those atomic shapes. A proposition with logical
    // structure is emitted as an obligation instead of being discharged by a
    // proof search inside lowering.
    let defer_contextual_proof = assumptions.should_defer_non_exact_loadability_obligations()
        && matches!(proposition, Proposition::MemoryLoadable { .. });
    if assumptions.proves_exact(&proposition)
        || !defer_contextual_proof && assumptions.proves_atomic_memory_or_resource(&proposition)
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

/// Whether `proposition` is one bare condition that the frozen condition
/// checker already decides with the value it asserts.
///
/// This is the migration's sanctioned replacement for a general prover call
/// on a bare `ConditionIs`: it adds no theory, traverses no logical
/// structure, and answers nothing about a proposition of any other shape.
fn bare_condition_is_decided(assumptions: &PureFactContext, proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return false;
    };
    if let ConditionTerm::Compare {
        format: MachineIntegerType::Int64,
        relation: CompareRelation::Equal,
        left,
        right,
    } = condition.native_compat()
        && *value
        && assumptions.uint64_values_known_equal(left, right)
    {
        crate::kernel::assumptions::record_implicit_consulted_premises(assumptions, proposition);
        return true;
    }
    if PureFactContext::decide_intrinsically(condition.native_compat()) == Some(*value) {
        return true;
    }
    !assumptions.should_defer_non_exact_condition_reasoning()
        && assumptions.decide(condition.native_compat()) == Some(*value)
}

/// Retain logical input evidence from the incoming checked context only.
/// Unlike call checking, retention must not redo memory/ownership derivation.
/// Machine and pointer equality use indexed evidence or intrinsic decisions;
/// the broader checker can enter memory resolution even for scalar terms.
pub(in crate::kernel) fn call_input_fact_is_already_known(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    let available = |side: &Proposition| {
        assumptions.states_required_goal(side)
            || assumptions.proves_exact(side)
            || assumptions.contains_known(side)
            || matches!(side, Proposition::ConditionIs(condition, value)
                if PureFactContext::decide_intrinsically(condition.native_compat()) == Some(*value)
                    || !matches!(condition.native_compat(),
                        ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, .. }
                        | ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::Equal, .. }
                        | ConditionTerm::PointerEqual(..)
                    | ConditionTerm::AddressEqual(..)
                        | ConditionTerm::AddressOffsetEqual(..))
                        && bare_condition_is_decided(assumptions, side))
    };
    crate::kernel::primitives::first_unavailable_connective_side(proposition, &available).is_none()
}

/// Discharge a required obligation using indexed facts, frozen atomic
/// checkers, and the same goal-local AND/OR rule as `close()`. This does
/// not unfold definitions, eliminate implications, or instantiate binders.
pub(in crate::kernel) fn required_obligation_is_exactly_discharged(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    let directly_available = |side: &Proposition| {
        assumptions.states_required_goal(side)
            || assumptions.proves_exact(side)
            || bare_condition_is_decided(assumptions, side)
            || assumptions.proves_atomic_memory_or_resource(side)
            || assumptions.contains_known(side)
    };
    // Preserve the existing direct route, including alpha-equivalent held
    // propositions and its shared lazy index. Walk connective structure only
    // when that route leaves the whole goal unresolved.
    if directly_available(proposition) {
        return true;
    }
    if !matches!(proposition, Proposition::And(..) | Proposition::Or(..)) {
        return false;
    }
    crate::kernel::primitives::first_unavailable_connective_side(proposition, &|side| {
        if matches!(side, Proposition::Or(..)) {
            // A held disjunction can shortcut the walk. Otherwise check its
            // leaves, without running builtin solving or alpha key creation
            // over every subtree of a long goal.
            return assumptions.has_disjunction_facts()
                && assumptions.contains_proposition_fact(side);
        }
        directly_available(side)
    })
    .is_none()
}

/// Emits one required verification condition, carrying the head chain the
/// lowering that built `proposition` recorded for it when there is one.
pub(in crate::kernel) fn add_required_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
    introductions: Option<&std::sync::Arc<LoweringIntroductions>>,
) {
    add_required_proof_obligation_with_context_and_site(
        obligations,
        assumptions,
        proposition,
        context,
        introductions,
        None,
        false,
        false,
    );
}

#[allow(clippy::too_many_arguments)]
fn add_required_proof_obligation_with_context_and_site(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
    introductions: Option<&std::sync::Arc<LoweringIntroductions>>,
    call_site: Option<&std::sync::Arc<CallRequirementSource>>,
    statement_entry_required: bool,
    live_view_write: bool,
) {
    // Suppression is the exact index, the frozen condition checker for a
    // proposition that is already one bare condition, or the retained atomic
    // memory/resource checkers. A required verification condition with
    // logical structure is emitted for an ordinary Surface tactic to
    // discharge.
    if !statement_entry_required
        && !assumptions.retains_required_obligations()
        && required_obligation_is_exactly_discharged(assumptions, &proposition)
    {
        return;
    }
    let mut obligation = ProofObligation::verification_condition(proposition)
        .with_shared_introductions(introductions)
        .with_statement_entry_required(statement_entry_required);
    obligation.live_view_write = live_view_write;
    if let Some(call_site) = call_site {
        obligation = obligation.with_call_requirement_site(call_site.clone());
    }
    let obligation = match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    };
    if let Some(existing) = obligations.iter_mut().find(|existing| {
        existing.proposition == obligation.proposition
            && existing.statement_entry_required == statement_entry_required
    }) {
        match (
            existing.call_requirement_site(),
            obligation.call_requirement_site(),
        ) {
            (None, Some(_)) => {
                // Replace the complete tuple, not only source metadata.
                *existing = obligation;
                return;
            }
            (Some(_), None) | (None, None) => return,
            (Some(existing), Some(incoming)) if existing.as_ref() == incoming.as_ref() => return,
            (Some(_), Some(_)) => {
                // Distinct source carriers remain finite alternatives. One
                // checked Have can discharge equal propositions from both.
                obligations.push(obligation);
                return;
            }
        }
    }
    obligations.push(obligation);
}

/// The same, suppressing only by the exact fact index, and carrying the same
/// recorded head chain.
pub(in crate::kernel) fn add_required_proof_obligation_without_search(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
    introductions: Option<&std::sync::Arc<LoweringIntroductions>>,
) {
    add_required_proof_obligation_without_search_and_site(
        obligations,
        assumptions,
        proposition,
        context,
        introductions,
        None,
        false,
        false,
    );
}

// An explicit obligation can name an already held machine comparison using
// shared observations. Select its original premise from the existing endpoint
// indexes; do not expose new aliases to general automatic condition search.
fn selected_obligation_is_stated(assumptions: &PureFactContext, proposition: &Proposition) -> bool {
    if assumptions.proves_exact(proposition) {
        return true;
    }
    match proposition {
        Proposition::ConditionIs(condition, truth) => {
            let Some(source) =
                assumptions.selected_comparison_source(condition.native_compat(), *truth)
            else {
                return false;
            };
            crate::kernel::assumptions::record_implicit_consulted_premises(assumptions, source);
            true
        }
        Proposition::And(left, right) => {
            selected_obligation_is_stated(assumptions, left)
                && selected_obligation_is_stated(assumptions, right)
        }
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn add_required_proof_obligation_without_search_and_site(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
    introductions: Option<&std::sync::Arc<LoweringIntroductions>>,
    call_site: Option<&std::sync::Arc<CallRequirementSource>>,
    statement_entry_required: bool,
    live_view_write: bool,
) {
    if !statement_entry_required
        && !assumptions.retains_required_obligations()
        && selected_obligation_is_stated(assumptions, &proposition)
    {
        return;
    }
    let mut obligation = if statement_entry_required {
        ProofObligation::verification_condition(proposition)
    } else {
        ProofObligation::new(proposition)
    }
    .with_shared_introductions(introductions)
    .with_statement_entry_required(statement_entry_required);
    obligation.live_view_write = live_view_write;
    if let Some(call_site) = call_site {
        obligation = obligation.with_call_requirement_site(call_site.clone());
    }
    let obligation = match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    };
    if let Some(existing) = obligations.iter_mut().find(|existing| {
        existing.proposition == obligation.proposition
            && existing.statement_entry_required == statement_entry_required
    }) {
        match (
            existing.call_requirement_site(),
            obligation.call_requirement_site(),
        ) {
            (None, Some(_)) => {
                *existing = obligation;
                return;
            }
            (Some(_), None) | (None, None) => return,
            (Some(existing), Some(incoming)) if existing.as_ref() == incoming.as_ref() => return,
            (Some(_), Some(_)) => {
                obligations.push(obligation);
                return;
            }
        }
    }
    obligations.push(obligation);
}

pub(in crate::kernel) fn append_required_proof_obligations(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_with_context_and_site(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
            obligation.shared_introductions(),
            obligation.call_requirement_site(),
            obligation.statement_entry_required,
            obligation.live_view_write,
        );
    }
}

pub(in crate::kernel) fn append_required_proof_obligations_without_search(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_without_search_and_site(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
            obligation.shared_introductions(),
            obligation.call_requirement_site(),
            obligation.statement_entry_required,
            obligation.live_view_write,
        );
    }
}

pub(in crate::kernel) fn append_required_proof_obligations_under_path_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    new_obligations: &[ProofObligation],
    facts: &(impl ExecutionFactSource + ?Sized),
    context_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        // This wrap adds head nodes in front of the obligation, so the
        // record it carries forward is the new guards followed by the chain
        // already recorded for the proposition underneath them.
        let (proposition, guards) = wrap_path_context_with_introductions(
            obligation.proposition().clone(),
            facts,
            context_obligations,
        );
        let introductions = obligation.introductions().map(|recorded| {
            let mut introductions = guards.clone();
            introductions.extend(recorded.iter().cloned());
            std::sync::Arc::new(introductions)
        });
        add_required_proof_obligation_with_context_and_site(
            obligations,
            assumptions,
            proposition,
            obligation.context(),
            introductions.as_ref(),
            obligation.call_requirement_site(),
            obligation.statement_entry_required,
            obligation.live_view_write,
        );
    }
}

pub(in crate::kernel) fn add_condition_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
    context: Option<&str>,
) -> Option<()> {
    if assumptions.proves_exact(&Proposition::condition_is(condition.clone(), value)) {
        return Some(());
    }
    if assumptions.proves_exact(&Proposition::condition_is(condition.clone(), !value)) {
        return None;
    }
    if let Some(known) = PureFactContext::decide_intrinsically(&condition) {
        return (known == value).then_some(());
    }
    if !assumptions.should_defer_non_exact_condition_reasoning()
        && let Some(known) = assumptions.decide(&condition)
    {
        return (known == value).then_some(());
    }

    if let Some(existing) = obligations
        .iter()
        .filter_map(|obligation| match obligation.proposition() {
            Proposition::ConditionIs(existing_condition, existing_value)
                if existing_condition.native_compat() == &condition =>
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

pub(in crate::kernel) fn merge_obligations(
    left: &[ProofObligation],
    right: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<Vec<ProofObligation>> {
    merge_obligations_with_changes(left, right, assumptions).map(|(obligations, _)| obligations)
}

fn merge_obligations_with_changes(
    left: &[ProofObligation],
    right: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<ProofObligation>, Vec<usize>)> {
    let mut obligations = left.to_vec();
    let mut changed = Vec::new();
    for obligation in right {
        if obligation.is_assumable() {
            // `right` was produced while executing under the complete left
            // path context. Preserve its path guard without asking the
            // general prover to reconsider it against an older memory
            // state. Exact and intrinsic contradictions still reject the
            // merge; non-exact cross-state reasoning cannot erase a path
            // that the executor just certified as possible.
            if assumptions.proves_exact(obligation.proposition()) {
                continue;
            }
            if let Some(index) = obligations
                .iter()
                .position(|existing| existing.proposition() == obligation.proposition())
            {
                let existing = &mut obligations[index];
                match (
                    existing.call_requirement_site(),
                    obligation.call_requirement_site(),
                ) {
                    (None, Some(_)) => {
                        // Replace the complete tuple, preserving the incoming
                        // source's context, introductions, and kind.
                        *existing = obligation.clone();
                        changed.push(index);
                        continue;
                    }
                    (Some(_), None) | (None, None) => continue,
                    (Some(existing), Some(incoming)) if existing.as_ref() == incoming.as_ref() => {
                        continue;
                    }
                    (Some(_), Some(_)) => {
                        // Distinct source carriers remain finite alternatives.
                    }
                }
            }
            if let Proposition::ConditionIs(condition, value) = obligation.proposition()
                && (assumptions
                    .proves_exact(&Proposition::condition_is(condition.clone(), !*value))
                    || PureFactContext::decide_intrinsically(condition.native_compat())
                        .is_some_and(|known| known != *value)
                    || obligations.iter().any(|existing| {
                        matches!(
                            existing.proposition(),
                            Proposition::ConditionIs(existing_condition, existing_value)
                                if existing_condition == condition && existing_value != value
                        )
                    }))
            {
                return None;
            }
            changed.push(obligations.len());
            obligations.push(obligation.clone());
        } else {
            // Preserve mandatory conditions as mandatory across composition.
            // Rebuilding with `ProofObligation::new` would make an unresolved
            // condition available as an assumption to later evaluation.
            changed.push(obligations.len());
            obligations.push(obligation.clone());
        }
    }
    Some((obligations, changed))
}

pub(in crate::kernel) fn merge_facts(
    left: &(impl ExecutionFactSource + ?Sized),
    right: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> Option<ExecutionFacts> {
    merge_facts_with_changes(left, right, assumptions).map(|(facts, _)| facts)
}

fn merge_facts_with_changes(
    left: &(impl ExecutionFactSource + ?Sized),
    right: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> Option<(ExecutionFacts, Vec<usize>)> {
    let mut changed = Vec::new();
    let prefix = left.persistent_facts();
    let suffix = right.persistent_facts();
    let mut facts = prefix.clone();
    let mut share_append = true;
    let mut appended = Vec::new();
    for (source_index, fact) in suffix.iter().enumerate() {
        let before = facts.len();
        // A certified fact is output of the checked producer, not a condition
        // selecting this path. Retain its record directly, including repeated
        // propositions with distinct producer metadata. Rechecking its truth
        // or finding a slot to overwrite scans the shared prefix and can lose
        // evidence the producer supplied. Logical deduplication belongs to the
        // receiving fact context; this stream keeps producer occurrences.
        if fact.is_certified() {
            crate::instrumentation::record_deterministic_work(1);
            facts.push(fact.clone());
            appended.push(source_index);
            changed.push(before);
            continue;
        }
        add_path_fact_with_visibility(
            &mut facts,
            assumptions,
            fact.proposition().clone(),
            fact.is_public(),
        )?;
        if facts.len() == before + 1 {
            share_append &= &facts[before] == fact;
            appended.push(source_index);
            changed.push(before);
        }
    }
    if share_append {
        // Validation may suppress redundant right facts, but it did not
        // change the prefix or normalize an appended fact. Retain the source
        // objects for the accepted delta instead of validation scratch copies.
        let mut combined = prefix;
        let accepted = suffix.selected(&appended);
        combined.extend_shared(&accepted);
        combined.retain_validated_membership(&facts);
        Some((combined, changed))
    } else {
        Some((facts, changed))
    }
}

pub(in crate::kernel) fn merge_execution_pure_facts_and_obligations(
    left_facts: &(impl ExecutionFactSource + ?Sized),
    left_obligations: &[ProofObligation],
    right_facts: &(impl ExecutionFactSource + ?Sized),
    right_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(ExecutionFacts, Vec<ProofObligation>)> {
    merge_execution_pure_facts_and_obligations_in(
        left_facts,
        left_obligations,
        right_facts,
        right_obligations,
        assumptions,
        None,
    )
}

/// [`merge_execution_pure_facts_and_obligations`] for a caller that already
/// built the left fragment's path context,
/// `assumptions_with_path_context(assumptions, left_facts, left_obligations)`,
/// to execute the right fragment under: the merge rechecks against that same
/// context, so building it again is the same work twice.
pub(in crate::kernel) fn merge_execution_pure_facts_and_obligations_under(
    left_facts: &(impl ExecutionFactSource + ?Sized),
    left_obligations: &[ProofObligation],
    right_facts: &(impl ExecutionFactSource + ?Sized),
    right_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    prefix_assumptions: &PureFactContext,
) -> Option<(ExecutionFacts, Vec<ProofObligation>)> {
    merge_execution_pure_facts_and_obligations_in(
        left_facts,
        left_obligations,
        right_facts,
        right_obligations,
        assumptions,
        Some(prefix_assumptions),
    )
}

fn merge_execution_pure_facts_and_obligations_in(
    left_facts: &(impl ExecutionFactSource + ?Sized),
    left_obligations: &[ProofObligation],
    right_facts: &(impl ExecutionFactSource + ?Sized),
    right_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    prefix_assumptions: Option<&PureFactContext>,
) -> Option<(ExecutionFacts, Vec<ProofObligation>)> {
    let facts = merge_facts(left_facts, right_facts, assumptions)?;
    // The right fragment was executed under the left fragment's path
    // context. Recheck its assumable obligations against that same context,
    // not against the older base assumptions. In particular, a verified call
    // can change a field that an entry-state branch constrained; checking a
    // post-call load guard against only the entry state can incorrectly
    // discard a valid successor path. Only an assumable obligation reads the
    // context, so a right fragment without one builds none.
    let built;
    let prefix_assumptions = match prefix_assumptions {
        Some(prefix_assumptions) => prefix_assumptions,
        None if right_obligations.iter().any(ProofObligation::is_assumable) => {
            built = assumptions_with_path_context(assumptions, left_facts, left_obligations);
            &built
        }
        None => assumptions,
    };
    let obligations = merge_obligations(left_obligations, right_obligations, prefix_assumptions)?;
    Some((facts, obligations))
}

/// A canonical merge and the context of its assumable members. Changed
/// positions include replacements of complete source-bearing tuples, not just
/// appended positions. Mandatory obligations are retained but never assumed.
pub(in crate::kernel) struct PreparedExecutionPath {
    pub facts: ExecutionFacts,
    pub obligations: Vec<ProofObligation>,
    pub assumptions: PureFactContext,
    pub changed_obligations: Vec<usize>,
}

/// Compose a pure lowering fragment under its already prepared left context.
/// The caller retains that persistent context between declarations, rather
/// than rebuilding every earlier fact and member at each declaration.
pub(in crate::kernel) fn merge_prepared_execution_path(
    left_facts: &ExecutionFacts,
    left_obligations: &[ProofObligation],
    right_facts: &ExecutionFacts,
    right_obligations: &[ProofObligation],
    base: &PureFactContext,
    prepared: &PureFactContext,
    effective: &PureFactContext,
) -> Option<PreparedExecutionPath> {
    let (facts, mut changed_facts) = merge_facts_with_changes(left_facts, right_facts, effective)?;
    let (obligations, mut changed_obligations) =
        merge_obligations_with_changes(left_obligations, right_obligations, effective)?;
    changed_facts.sort_unstable();
    changed_facts.dedup();
    changed_obligations.sort_unstable();
    changed_obligations.dedup();
    // Invariant reading is pure. Keep the general merge's ordering if this
    // helper is later used with an effect-bearing fragment: post-effect facts
    // can supersede an entry-state condition, unlike a pure monotone extension.
    let assumptions = if right_facts.iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::MemoryMutatesOnly { .. }
                | Proposition::MemoryEffectSummary { .. }
                | Proposition::HeapAllocationFreed { .. }
        )
    }) {
        assumptions_with_path_context(base, &facts, &obligations)
    } else {
        count_context_rebuild_entries(changed_facts.len() + changed_obligations.len());
        let mut context = prepared.clone();
        for index in changed_facts {
            context = context.assume_execution_pure_fact(&facts[index]);
        }
        for &index in &changed_obligations {
            if obligations[index].is_assumable() {
                context = context.assume_proposition(obligations[index].proposition().clone());
            }
        }
        context
    };
    Some(PreparedExecutionPath {
        facts,
        obligations,
        assumptions,
        changed_obligations,
    })
}

pub(in crate::kernel) fn decide_with_facts(
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
    condition: &ConditionTerm,
) -> Option<bool> {
    [true, false]
        .into_iter()
        .find(|value| {
            assumptions.proves_exact(&Proposition::condition_is(condition.clone(), *value))
        })
        .or_else(|| {
            // Exact observations retain their operands while selecting the
            // comparison reading. Recurse only when that reading changes the
            // condition, keeping execution's bounded query and cycle boundary.
            let view = crate::kernel::machine_integer::comparison::native_comparison_view(
                condition, true,
            )?;
            let (reading, truth) = view.retained_condition();
            if &reading == condition { return None; }
            decide_with_facts(assumptions, facts, &reading).map(|value| value == truth)
        })
        .or_else(|| assumptions.decide_signed_byte_equality_from_exact_fact(condition))
        .or_else(|| PureFactContext::decide_intrinsically(condition))
        .or_else(|| assumptions.known_condition_value(condition))
        .or_else(|| {
            // Direct path facts use the same retained comparison identity as
            // the context's exact index. Select an existing source before
            // constructing a difference graph; no operand is materialized.
            facts.fact_iter().find_map(|fact| match fact.proposition() {
                Proposition::ConditionIs(existing, value) if existing.native_compat() == condition => Some(*value),
                source => [true, false].into_iter().find(|truth| {
                    crate::kernel::assumptions::observation_comparisons::same_comparison(
                        condition, *truth, source,
                    )
                }),
            })
        })
        .or_else(|| {
            let extra = facts
                .fact_iter()
                .filter_map(|fact| match fact.proposition() {
                    Proposition::ConditionIs(condition, value) => Some((condition.native_compat().clone(), *value)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assumptions.difference_decision(condition, &extra)
        })
        .or_else(|| {
            // With no path facts, the preceding context and intrinsic queries
            // already covered both possible bases. Rebuilding an empty graph
            // here would discard their prefix work on every unresolved guard.
            let mut path_facts = facts.fact_iter().peekable();
            path_facts.peek()?;
            let merged = path_facts.fold(
                // Address comparisons need the checked aliases when adding
                // their two-holder separation projection. Keep the deferred
                // policy; other comparisons retain their existing cheap path.
                if !assumptions.should_defer_non_exact_condition_reasoning()
                    || matches!(condition, ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::Equal, left: a, right: b }
                        if a.address_pointer().is_some() && b.address_pointer().is_some())
                {
                    assumptions.clone()
                } else {
                    PureFactContext::new()
                },
                |assumptions, fact| assumptions.assume_proposition(fact.proposition().clone()),
            );
            // A composition a comparison assumed as a path fact is read by
            // the keyed pointer rules there.
            merged.difference_decision(condition, &[])
        })
}

#[cfg(test)]
thread_local! {
    static CONTEXT_REBUILD_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static CONTRACT_PATH_CONTEXT_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn record_contract_path_context_entries(entries: usize) {
    CONTRACT_PATH_CONTEXT_ENTRIES.with(|count| count.set(count.get() + entries));
}

#[cfg(test)]
pub(crate) fn contract_path_context_entries() -> usize {
    CONTRACT_PATH_CONTEXT_ENTRIES.with(std::cell::Cell::get)
}

/// Counts, in test builds, the entries a fact context built from a list
/// assumes (`assumptions_with_path_context`, `assumptions_with_propositions`,
/// `PropositionSource::pure_context`, `PureFactStore::from_ordered`, and the
/// contexts a `PureFactList` extends). The work itself is charged where
/// every context is built, one unit per fact
/// (`PureFactContext::assume_proposition`), so a caller that rebuilds a
/// context from a growing list once per item shows as quadratic work; this
/// count lets a scaling regression pin the builds alone.
pub(crate) fn count_context_rebuild_entries(_entries: usize) {
    #[cfg(test)]
    record_context_entries_for_tests(_entries);
}

/// Counts, in test builds, the entries of a context build that is charged
/// nothing (`PureFactContext::assume_proposition_uncharged`): a known
/// violation of the complexity contract, listed in
/// `docs/internals/verification-efficiency.md`, whose charge would fail a
/// scaling regression until its representation changes.
pub(crate) fn count_uncharged_context_entries(_entries: usize) {
    #[cfg(test)]
    record_context_entries_for_tests(_entries);
}

#[cfg(test)]
fn record_context_entries_for_tests(entries: usize) {
    CONTEXT_REBUILD_ENTRIES.with(|count| count.set(count.get() + entries));
}

/// The context entries built so far on this thread, charged or not.
#[cfg(test)]
pub(crate) fn context_rebuild_entries() -> usize {
    CONTEXT_REBUILD_ENTRIES.with(std::cell::Cell::get)
}

pub(in crate::kernel) fn assumptions_with_path_context(
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> PureFactContext {
    count_context_rebuild_entries(facts.len() + obligations.len());
    let mut assumptions = assumptions.clone();
    for fact in facts.fact_iter() {
        assumptions = assumptions.assume_execution_pure_fact(fact);
    }
    for obligation in obligations {
        if obligation.is_assumable() {
            assumptions = assumptions.assume_proposition(obligation.proposition().clone());
        }
    }
    assumptions
}

pub(in crate::kernel) fn assumptions_with_propositions(
    assumptions: &PureFactContext,
    propositions: &[Proposition],
) -> PureFactContext {
    count_context_rebuild_entries(propositions.len());
    let mut assumptions = assumptions.clone();
    for proposition in propositions {
        assumptions = assumptions.assume_proposition(proposition.clone());
    }
    assumptions
}

#[cfg(test)]
mod sequence_equality_tests {
    use super::*;

    fn singleton(value: u32) -> SequenceTerm {
        SequenceTerm {
            element_type: Some(ProgramType::Int32),
            node: std::sync::Arc::new(SequenceTermNode::Literal(
                vec![crate::kernel::api::int32(value)].into(),
            )),
        }
    }

    fn concatenate(left: SequenceTerm, right: SequenceTerm) -> SequenceTerm {
        SequenceTerm {
            element_type: Some(ProgramType::Int32),
            node: std::sync::Arc::new(SequenceTermNode::Concat(left, right)),
        }
    }

    #[test]
    fn associative_sequence_equality_is_iterative_across_rope_shapes() {
        for size in [8u32, 64, 512] {
            let mut left_associated = singleton(0);
            for value in 1..size {
                left_associated = concatenate(left_associated, singleton(value));
            }

            let mut right_associated = singleton(size - 1);
            for value in (0..size - 1).rev() {
                right_associated = concatenate(singleton(value), right_associated);
            }

            assert!(solve_builtin_prop(&Proposition::Equal(
                Term::Sequence(left_associated),
                Term::Sequence(right_associated),
            )));
        }
    }
}

#[cfg(test)]
mod mandatory_integer_obligation_tests {
    use super::*;

    fn call_source(interface: &str, ordinal: usize) -> std::sync::Arc<CallRequirementSource> {
        std::sync::Arc::new(CallRequirementSource::new(
            std::sync::Arc::new(CallRequirementSite::for_requirement(
                "callee",
                interface,
                0,
                &[],
                &SymbolicMemory::new(),
            )),
            ordinal,
            Some(ordinal),
            true,
            None,
        ))
    }

    #[test]
    fn required_obligation_append_variants_preserve_call_source_and_reject_conflicts() {
        let proposition = Proposition::Predicate {
            name: "required".to_string(),
            arguments: vec![],
        };
        let source = call_source("selected", 0);
        let required = ProofObligation::verification_condition(proposition.clone())
            .with_call_requirement_site(source.clone());
        let assumptions = PureFactContext::new();

        let appenders: [fn(&mut Vec<ProofObligation>, &PureFactContext, &[ProofObligation]); 2] = [
            append_required_proof_obligations,
            append_required_proof_obligations_without_search,
        ];
        for append in appenders {
            let mut obligations = Vec::new();
            append(
                &mut obligations,
                &assumptions,
                std::slice::from_ref(&required),
            );
            assert!(std::sync::Arc::ptr_eq(
                obligations[0]
                    .call_requirement_site()
                    .expect("append preserves call source"),
                &source
            ));
        }

        let mut under_path = Vec::new();
        append_required_proof_obligations_under_path_context(
            &mut under_path,
            &assumptions,
            std::slice::from_ref(&required),
            &[],
            &[],
        );
        assert!(under_path[0].call_requirement_site().is_some());

        let conflicting = ProofObligation::verification_condition(proposition.clone())
            .with_call_requirement_site(call_source("other", 0));
        append_required_proof_obligations(
            &mut under_path,
            &assumptions,
            std::slice::from_ref(&conflicting),
        );
        assert!(
            under_path[0].call_requirement_site().is_some()
                && under_path[1].call_requirement_site().is_some(),
            "conflicting duplicate call sites must remain source-bearing"
        );
        assert_eq!(under_path.len(), 2);

        let same_site_different_ordinal = ProofObligation::verification_condition(proposition)
            .with_call_requirement_site(call_source("selected", 1));
        append_required_proof_obligations(
            &mut under_path,
            &assumptions,
            std::slice::from_ref(&same_site_different_ordinal),
        );
        assert_eq!(under_path.len(), 3);
        assert!(under_path[2].call_requirement_site().is_some());

        let carrierless_duplicate =
            ProofObligation::verification_condition(Proposition::Predicate {
                name: "required".to_string(),
                arguments: vec![],
            });
        append_required_proof_obligations(
            &mut under_path,
            &assumptions,
            std::slice::from_ref(&carrierless_duplicate),
        );
        assert_eq!(under_path.len(), 3);
        assert!(
            under_path
                .iter()
                .all(|obligation| obligation.call_requirement_site().is_some())
        );

        let tuple_proposition = Proposition::Predicate {
            name: "tuple".to_string(),
            arguments: vec![],
        };
        let incoming_introductions =
            std::sync::Arc::new(vec![LoweringIntroduction::WrittenNegation]);
        let incoming_source = call_source("incoming", 2);
        let mut tuple_obligations = vec![
            ProofObligation::verification_condition(tuple_proposition.clone())
                .with_context("old context")
                .with_introductions(vec![LoweringIntroduction::PathFactGuard]),
        ];
        add_required_proof_obligation_with_context_and_site(
            &mut tuple_obligations,
            &assumptions,
            tuple_proposition,
            Some("incoming context"),
            Some(&incoming_introductions),
            Some(&incoming_source),
            false,
            false,
        );
        assert_eq!(tuple_obligations.len(), 1);
        assert_eq!(
            tuple_obligations[0].context.as_deref(),
            Some("incoming context")
        );
        assert_eq!(
            tuple_obligations[0].introductions.as_deref(),
            Some(incoming_introductions.as_ref())
        );
        assert!(std::sync::Arc::ptr_eq(
            tuple_obligations[0]
                .call_requirement_site()
                .expect("replacement keeps incoming source"),
            &incoming_source
        ));
    }

    // A cached path must retain canonical source metadata and must not turn
    // an unresolved verification condition into a fact for the next member.
    #[test]
    fn prepared_path_delta_matches_fresh_context_with_retained_producer_records() {
        let predicate = |name: &str| Proposition::Predicate {
            name: name.to_string(),
            arguments: vec![],
        };
        let old_fact = ExecutionPureFact::new(predicate("old fact"));
        let upgraded = ExecutionPureFact::certified(old_fact.proposition().clone());
        let new_fact = ExecutionPureFact::new(predicate("new fact"));
        let left_facts = ExecutionFacts::from(vec![old_fact]);
        let right_facts = ExecutionFacts::from(vec![upgraded.clone(), new_fact.clone()]);
        let mandatory = ProofObligation::verification_condition(Proposition::condition_is(
            ConditionTerm::Constant(false),
            true,
        ))
        .with_context("still owed");
        let replaceable = ProofObligation::verification_condition(predicate("replacement"))
            .with_context("old source")
            .with_introductions(vec![LoweringIntroduction::PathFactGuard]);
        let source = call_source("incoming", 2);
        let incoming = ProofObligation::new(predicate("replacement"))
            .with_context("incoming source")
            .with_introductions(vec![LoweringIntroduction::WrittenNegation])
            .with_call_requirement_site(source.clone());
        let left_obligations = vec![replaceable, mandatory.clone()];
        let right_obligations = vec![incoming.clone(), mandatory.clone()];
        let base = PureFactContext::new();
        let prepared = assumptions_with_path_context(&base, &left_facts, &left_obligations);
        let effective = prepared
            .clone()
            .defer_non_exact_condition_reasoning()
            .defer_non_exact_loadability_obligations();
        let merged = merge_prepared_execution_path(
            &left_facts,
            &left_obligations,
            &right_facts,
            &right_obligations,
            &base,
            &prepared,
            &effective,
        )
        .unwrap();
        let (fresh_facts, fresh_obligations) = merge_execution_pure_facts_and_obligations(
            &left_facts,
            &left_obligations,
            &right_facts,
            &right_obligations,
            &effective,
        )
        .unwrap();
        assert_eq!(merged.facts, fresh_facts);
        assert_eq!(merged.facts.len(), 3);
        assert_eq!(merged.facts[0], left_facts[0]);
        assert_eq!(merged.facts[1], upgraded);
        assert_eq!(merged.facts[2], new_fact);
        assert_eq!(merged.obligations, fresh_obligations);
        assert_eq!(merged.changed_obligations, vec![0, 2]);
        assert_eq!(
            merged.obligations[0].introductions(),
            incoming.introductions()
        );
        assert!(std::sync::Arc::ptr_eq(
            merged.obligations[0].call_requirement_site().unwrap(),
            &source
        ));
        assert_eq!(
            merged.assumptions,
            assumptions_with_path_context(&base, &fresh_facts, &fresh_obligations)
        );
        assert!(!merged.assumptions.proves_exact(mandatory.proposition()));
        assert!(merged.assumptions.proves_exact(incoming.proposition()));
    }

    #[test]
    fn prepared_path_effect_fragment_keeps_fresh_rebuild_ordering() {
        let condition = ConditionTerm::equal(
            MachineTerm::Variable(Variable(912_347)),
            MachineTerm::constant(3),
        );
        let base = PureFactContext::new();
        let left = vec![ProofObligation::condition(condition.clone(), true)];
        let prepared = assumptions_with_path_context(&base, &[], &left);
        let memory = SymbolicMemory::new();
        let right = ExecutionFacts::from(vec![
            ExecutionPureFact::new(Proposition::MemoryMutatesOnly {
                before: memory.clone(),
                after: memory,
                writes: vec![],
            }),
            ExecutionPureFact::certified(Proposition::condition_is(condition, false)),
        ]);
        let merged = merge_prepared_execution_path(
            &ExecutionFacts::new(),
            &left,
            &right,
            &[],
            &base,
            &prepared,
            &prepared,
        )
        .unwrap();
        let (facts, obligations) = merge_execution_pure_facts_and_obligations(
            &ExecutionFacts::new(),
            &left,
            &right,
            &[],
            &prepared,
        )
        .unwrap();
        assert_eq!(merged.facts, facts);
        assert_eq!(merged.obligations, obligations);
        assert_eq!(
            merged.assumptions,
            assumptions_with_path_context(&base, &facts, &obligations)
        );
    }

    #[test]
    fn prepared_path_delta_rejects_a_conflicting_pure_successor() {
        let condition = ConditionTerm::equal(
            MachineTerm::Variable(Variable(912_345)),
            MachineTerm::constant(3),
        );
        let base = PureFactContext::new();
        let left = vec![ProofObligation::condition(condition.clone(), true)];
        let prepared = assumptions_with_path_context(&base, &[], &left);
        let right = ExecutionFacts::from(vec![ExecutionPureFact::new(Proposition::condition_is(
            condition, false,
        ))]);
        assert!(
            merge_prepared_execution_path(
                &ExecutionFacts::new(),
                &left,
                &right,
                &[],
                &base,
                &prepared,
                &prepared,
            )
            .is_none()
        );
    }

    #[test]
    fn integer_conversion_obligation_merge_preserves_kind_and_context() {
        let proposition = Proposition::condition_is(ConditionTerm::Constant(false), true);
        let required = ProofObligation::verification_condition(proposition.clone())
            .with_context("Integer argument definedness");
        let base = PureFactContext::new();
        for (left, right) in [
            (vec![required.clone()], vec![]),
            (vec![], vec![required.clone()]),
        ] {
            let merged = merge_obligations(&left, &right, &base).unwrap();
            assert_eq!(merged, vec![required.clone()]);
            let context = assumptions_with_path_context(&base, &[], &merged);
            assert!(!context.proves_exact(&proposition));
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/reasoning/path_facts/mandatory_integer_obligation_tests.rs"
        );
    }
}

#[cfg(test)]
mod native_observation_guard_tests {
    use super::*;

    #[test]
    fn explicit_obligations_reuse_selected_comparison_sources() {
        use crate::kernel::assumptions::{
            capture_implicit_consulted_premises, collect_consulted_premises,
        };
        use crate::kernel::machine_integer::comparison::condition_for_operand_views;
        use crate::kernel::{
            KernelTermExport, KernelTermImport, MachineBinaryOp, MachineOperandView,
        };
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let variable = |id| MachineTerm::Variable(Variable(id));
            let expression = MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: Box::new(variable(850_010)),
                right: Box::new(variable(850_011)),
            };
            let shared = KernelTermImport::default()
                .machine_arithmetic(format, &expression)
                .unwrap();
            let right = variable(850_012);
            for relation in [
                CompareRelation::Equal,
                CompareRelation::LessThan,
                CompareRelation::GreaterEqual,
            ] {
                let native = ConditionTerm::machine_compare(
                    format,
                    relation,
                    expression.clone(),
                    right.clone(),
                );
                let observed = condition_for_operand_views(
                    format,
                    relation,
                    [
                        MachineOperandView::Shared(&shared),
                        MachineOperandView::Legacy(&right),
                    ],
                );
                for truth in [false, true] {
                    let source = Proposition::condition_is(native.clone(), truth);
                    let query = Proposition::condition_is(observed.clone(), truth);
                    let parent = PureFactContext::new();
                    let context = parent.clone().assume_proposition(source.clone());
                    let discharge = |context: &PureFactContext, query| {
                        let mut obligations = Vec::new();
                        add_required_proof_obligation_without_search(
                            &mut obligations,
                            context,
                            query,
                            None,
                            None,
                        );
                        obligations
                    };
                    let exports = KernelTermExport::machine_export_count();
                    let (obligations, used) = collect_consulted_premises(|| {
                        capture_implicit_consulted_premises(|| discharge(&context, query.clone()))
                    });
                    assert!(obligations.is_empty(), "{format:?} {relation:?} {truth}");
                    assert!(used.contains(&source));
                    assert!(!context.contains_assumed_exact(&query));
                    assert_eq!(discharge(&parent, query.clone()).len(), 1);
                    assert_eq!(
                        discharge(
                            &context.clone().retaining_required_obligations(),
                            query.clone()
                        )
                        .len(),
                        1
                    );
                    assert_eq!(
                        discharge(
                            &context,
                            Proposition::condition_is(observed.clone(), !truth)
                        )
                        .len(),
                        1
                    );
                    let missing = Proposition::condition_is(
                        ConditionTerm::equal(variable(850_013), variable(850_014)),
                        true,
                    );
                    assert_eq!(
                        discharge(
                            &context,
                            Proposition::And(Box::new(query.clone()), Box::new(missing))
                        )
                        .len(),
                        1
                    );
                    assert!(
                        discharge(
                            &context,
                            Proposition::And(Box::new(query.clone()), Box::new(query))
                        )
                        .is_empty()
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    fn equalities(ty: MachineIntegerType) -> (ConditionTerm, ConditionTerm) {
        let value = MachineTerm::Variable(Variable(912_801));
        let native = match ty {
            MachineIntegerType::Int32 | MachineIntegerType::UInt32 => {
                ConditionTerm::equal(value.clone(), MachineTerm::constant(0))
            }
            MachineIntegerType::Int64 => {
                ConditionTerm::int64_equal(value.clone(), MachineTerm::int64_constant(0))
            }
            MachineIntegerType::UInt64 => {
                ConditionTerm::uint64_equal(value.clone(), MachineTerm::uint64_constant(0))
            }
            _ => unreachable!(),
        };
        let observed = ConditionTerm::integer_equal(
            IntegerTerm::from_machine(ty, value).unwrap(),
            IntegerTerm::constant_i64(0),
        );
        (native, observed)
    }

    #[test]
    fn bounded_integer_guards_use_native_facts_in_both_truth_directions() {
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let _session = crate::kernel::VerificationSession::enter();
            let (native, observed) = equalities(ty);
            let empty = PureFactContext::new().defer_non_exact_condition_reasoning();
            let no_path_facts = ExecutionFacts::new();
            assert_eq!(decide_with_facts(&empty, &no_path_facts, &observed), None);
            let ConditionTerm::IntegerEqual(left, right) = &observed else {
                unreachable!()
            };
            let not_equal =
                ConditionTerm::integer_not_equal(left.as_ref().clone(), right.as_ref().clone());
            let other = ConditionTerm::integer_equal(
                IntegerTerm::from_machine(ty, MachineTerm::Variable(Variable(912_802))).unwrap(),
                IntegerTerm::constant_i64(0),
            );
            for truth in [false, true] {
                let context = empty.clone().assume_condition(native.clone(), truth);
                assert_eq!(
                    decide_with_facts(&context, &no_path_facts, &observed),
                    Some(truth)
                );
                assert_eq!(
                    decide_with_facts(&context, &no_path_facts, &not_equal),
                    Some(!truth)
                );
                assert_eq!(decide_with_facts(&context, &no_path_facts, &other), None);
                let path = ExecutionFacts::from(vec![ExecutionPureFact::new(
                    Proposition::condition_is(native.clone(), truth),
                )]);
                assert_eq!(decide_with_facts(&empty, &path, &observed), Some(truth));
                assert_eq!(decide_with_facts(&empty, &path, &not_equal), Some(!truth));
            }
        }
    }

    fn fresh_arithmetic_guards(ty: MachineIntegerType, require_unexported: bool) {
        use crate::kernel::{
            KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, SharedMachineIntegerTerm,
        };
        for truth in [None, Some(false), Some(true)] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable =
                |id| KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
            let product = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Multiply,
                [variable(984001), variable(984002)],
            );
            let observed = |root| {
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap())
            };
            let a = observed(product);
            let b = observed(variable(984003));
            let goal = ConditionTerm::integer_equal(a.clone(), b.clone());
            let opposite = ConditionTerm::integer_not_equal(a, b);
            let source = ConditionTerm::machine_compare(
                ty,
                CompareRelation::Equal,
                MachineTerm::logical_machine_binary(
                    ty,
                    MachineBinaryOp::Multiply,
                    MachineTerm::Variable(Variable(984001)),
                    MachineTerm::Variable(Variable(984002)),
                ),
                MachineTerm::Variable(Variable(984003)),
            );
            let exports = KernelTermExport::machine_export_count();
            let empty = PureFactContext::new().defer_non_exact_condition_reasoning();
            let context = truth.map_or_else(
                || empty.clone(),
                |truth| empty.clone().assume_condition(source.clone(), truth),
            );
            let no_path = ExecutionFacts::new();
            assert_eq!(
                decide_with_facts(&context, &no_path, &goal),
                truth,
                "{ty:?}"
            );
            assert_eq!(
                decide_with_facts(&context, &no_path, &opposite),
                truth.map(|x| !x)
            );
            if let Some(truth) = truth {
                let path = ExecutionFacts::from(vec![ExecutionPureFact::new(
                    Proposition::condition_is(source, truth),
                )]);
                assert_eq!(decide_with_facts(&empty, &path, &goal), Some(truth));
                assert_eq!(decide_with_facts(&empty, &path, &opposite), Some(!truth));
            }
            if require_unexported {
                assert_eq!(KernelTermExport::machine_export_count(), exports, "{ty:?}");
            }
        }
    }

    #[test]
    fn fresh_word_guards_keep_operands_on_success_and_refusal() {
        for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            fresh_arithmetic_guards(ty, true);
        }
    }

    #[test]
    fn fresh_wide_guards_preserve_native_results() {
        // The general intrinsic wide-equality dispatcher remains a separate
        // migration boundary; this pins the execution adapter's verdicts.
        for ty in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            fresh_arithmetic_guards(ty, false);
        }
    }

    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/reasoning/path_facts/native_observation_guard_tests.rs"
        );
    }
}

#[cfg(test)]
mod shared_reconstruction_tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineIntegerType as T, MachineOperandView as V,
        SharedMachineIntegerTerm as S,
    };

    fn scaled(value: S, width: i64, wide: bool) -> AddressOffset {
        if wide {
            AddressOffset::Int64Scaled {
                value,
                byte_width: width,
                unsigned: true,
            }
        } else {
            AddressOffset::Int32Scaled {
                value,
                byte_width: width,
            }
        }
    }

    #[test]
    fn shared_scaled_element_guards_preserve_signedness_and_stride() {
        for ty in [T::Int32, T::Int64, T::UInt64] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable = MachineTerm::Variable(Variable(1081101));
            let root = KernelTerm::retained_machine_operand(ty, V::Legacy(&variable));
            let root = KernelTerm::machine_binary_shared(
                ty,
                crate::kernel::MachineBinaryOp::Add,
                [root.clone(), root],
            );
            let index = S::from_shared(ty, root).unwrap();
            let offset = if ty == T::Int32 {
                scaled(index.clone(), 8, false)
            } else {
                AddressOffset::Int64Scaled {
                    value: index.clone(),
                    byte_width: 8,
                    unsigned: ty == T::UInt64,
                }
            };
            let exports = KernelTermExport::machine_export_count();
            let element = scaled_element_offset(&offset).unwrap();
            assert_eq!(element.signed, ty != T::UInt64);
            assert_eq!(element.stride, 8);
            let count = MachineTerm::uint64_constant(10);
            let guards = wide_index_bound_conditions(
                &element.index,
                element.signed,
                &count,
                true,
                &PureFactContext::new(),
            );
            assert_eq!(guards.len(), if element.signed { 2 } else { 1 });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!index.has_boxed_operand());
        }
    }

    #[test]
    fn shared_offset_reconstruction_keeps_residues_and_width_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1018201));
        let index = S::index(
            T::Int32,
            MachineTerm::add(x.clone(), MachineTerm::constant(1)),
        );
        let offset = scaled(index.clone(), 4, false);
        let wide = scaled(S::index(T::Int64, MachineTerm::uint64_from_32(x)), 4, true);
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(shared_element_index_from_offset(&offset, 4), Some(index));
        assert!(shared_element_index_from_offset(&offset, 0).is_none());
        assert!(shared_element_index_from_offset(&offset, 8).is_none());
        let bytes = shared_byte_offset_from_pointer_offset(&offset).unwrap();
        assert!(matches!(
            bytes.operand_view().binary(),
            Some((T::Int32, MachineBinaryOp::Multiply, _))
        ));
        assert!(shared_byte_offset_from_pointer_offset(&wide).is_none());
        assert!(shared_element_index_from_offset(&wide, 4).is_none());
        let zero = scaled(
            S::index(T::Int64, MachineTerm::uint64_constant(u64::MAX)),
            0,
            true,
        );
        assert_eq!(
            shared_byte_offset_from_pointer_offset(&zero)
                .unwrap()
                .operand_view()
                .word32_constant(),
            Some(0)
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_wide_element_projection_requires_full_width_support() {
        let _session = crate::kernel::VerificationSession::enter();
        let root = KernelTerm::machine_binary_shared(
            T::UInt64,
            MachineBinaryOp::Add,
            [
                KernelTerm::variable(
                    KernelType::Program(T::UInt64.program_type()),
                    Variable(1018202),
                ),
                KernelTerm::variable(
                    KernelType::Program(T::UInt64.program_type()),
                    Variable(1018203),
                ),
            ],
        );
        let offset = scaled(V::Shared(&root).retain(T::Int64), 8, true);
        let limit = MachineTerm::uint64_constant(i32::MAX as u64);
        let bound = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            T::UInt64,
            CompareRelation::LessEqual,
            [V::Shared(&root), V::Legacy(&limit)],
        );
        let empty = PureFactContext::new();
        let bounded = empty.clone().assume_condition(bound.clone(), true);
        let low = root.checking_legacy_machine_conversion(T::UInt64, T::UInt32);
        let low_bound = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            T::UInt32,
            CompareRelation::LessEqual,
            [
                V::Shared(&low),
                V::Legacy(&MachineTerm::constant(i32::MAX as u32)),
            ],
        );
        let low_only = empty.clone().assume_condition(low_bound, true);
        let exports = KernelTermExport::machine_export_count();
        assert!(shared_element_index_from_offset_with_facts(&offset, 8, &bounded).is_some());
        for facts in [&empty, &low_only] {
            assert!(shared_element_index_from_offset_with_facts(&offset, 8, facts).is_none());
        }
        assert!(shared_element_index_from_offset_with_facts(&offset, 4, &bounded).is_none());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_rebuilt_element_sum_needs_nonoverflow_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1018204));
        let y = MachineTerm::Variable(Variable(1018205));
        let offset = AddressOffset::Add(
            Box::new(scaled(S::index(T::Int32, x.clone()), 4, false)),
            Box::new(scaled(S::index(T::Int32, y.clone()), 4, false)),
        );
        let empty = PureFactContext::new();
        let mut bounded = empty.clone();
        for v in [x, y] {
            bounded = bounded
                .assume_condition(
                    ConditionTerm::signed_greater_equal(v.clone(), MachineTerm::constant(0)),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(v, MachineTerm::constant(100)),
                    true,
                );
        }
        let exports = KernelTermExport::machine_export_count();
        assert!(!empty.element_index_rebuild_is_exact_for_width(&offset, 4));
        assert!(bounded.element_index_rebuild_is_exact_for_width(&offset, 4));
        let wraps = AddressOffset::Add(
            Box::new(AddressOffset::Constant(i64::from(i32::MAX) * 4)),
            Box::new(AddressOffset::Constant(4)),
        );
        assert!(!empty.element_index_rebuild_is_exact_for_width(&wraps, 4));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/reasoning/path_facts/shared_reconstruction_tests.rs");
    }
}

#[cfg(test)]
mod certified_merge_tests {
    use super::*;

    #[test]
    fn certified_outputs_do_not_become_path_guards() {
        let condition = |id| Proposition::condition_is(ConditionTerm::Variable(Variable(id)), true);
        let branch = condition(991_010);
        let produced = condition(991_011);
        let required = condition(991_012);
        let goal = condition(991_013);
        let facts: ExecutionFacts = vec![
            ExecutionPureFact::new(branch.clone()),
            ExecutionPureFact::certified(produced.clone()),
        ]
        .into();
        let obligations = vec![ProofObligation::verification_condition(required.clone())];
        let (wrapped, introductions) =
            wrap_path_context_with_introductions(goal.clone(), &facts, &obligations);
        assert_eq!(
            wrapped,
            Proposition::Implies(
                Box::new(branch),
                Box::new(Proposition::Implies(Box::new(required), Box::new(goal)))
            )
        );
        assert_eq!(
            introductions,
            vec![
                LoweringIntroduction::PathFactGuard,
                LoweringIntroduction::ObligationGuard,
            ]
        );
        assert_eq!(facts[1].proposition(), &produced);
        assert!(
            assumptions_with_path_context(&PureFactContext::new(), &facts, &[])
                .proves_exact(&produced)
        );
    }

    #[test]
    fn certified_merge_keeps_already_known_facts_and_the_original_prefix() {
        let condition = ConditionTerm::equal(
            MachineTerm::Variable(Variable(1024000)),
            MachineTerm::constant(7),
        );
        let proposition = Proposition::condition_is(condition.clone(), true);
        let context = PureFactContext::new().assume_condition(condition, true);
        let prefix: ExecutionFacts = vec![ExecutionPureFact::new(proposition.clone())].into();
        let produced: ExecutionFacts = vec![ExecutionPureFact::certified(proposition)].into();
        let (merged, changed) = merge_facts_with_changes(&prefix, &produced, &context).unwrap();
        assert_eq!(changed, vec![1]);
        assert_eq!(merged.len(), 2);
        assert!(!prefix[0].is_certified());
        assert!(!merged[0].is_certified());
        assert!(merged[1].is_certified());
        assert!(std::sync::Arc::ptr_eq(
            merged.plain_fact_at(0).unwrap(),
            prefix.plain_fact_at(0).unwrap(),
        ));
        assert!(std::sync::Arc::ptr_eq(
            merged.plain_fact_at(1).unwrap(),
            produced.plain_fact_at(0).unwrap(),
        ));
        let retained = assumptions_with_path_context(&context, &merged, &[]);
        assert!(retained.proves_exact(merged[1].proposition()));
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/reasoning/path_facts/certified_merge_tests.rs");
    }
}
