//! Goal-local computation for a simple proof leaf.
//!
//! The `computes_leaf` entry point receives no fact context. Reads, calls,
//! folds, and symbolic matches remain opaque operands in that entry point;
//! it has no memory resolution, unfolding, or atomic-prover fallback. Legacy
//! normalization shares arithmetic below but supplies its own atom key.

use crate::kernel::*;
use crate::kernel::{
    constant_i64, constant_u32, constant_u64, int32_constant, int64_constant, uint64_constant,
};

/// Whether this leaf is true by direct computation or state metadata.
/// Positive connectives belong to the caller's structural walk. Negated
/// connective trees may compute, but implications and quantifiers always
/// require their ordinary introduction steps.
pub(crate) fn computes_leaf(goal: &Proposition) -> bool {
    // The caller walks positive connectives once, mixing facts and computed
    // leaves. Rewalking each positive subtree here would be quadratic on a
    // nested conjunction with one noncomputational leaf. Negated connectives
    // are atomic inputs to that caller, and compute structurally below.
    !matches!(goal, Proposition::And(..) | Proposition::Or(..))
        && proposition_value(goal) == Some(true)
}

fn proposition_value(goal: &Proposition) -> Option<bool> {
    crate::instrumentation::record_deterministic_work(1);
    match goal {
        Proposition::Not(body) => proposition_value(body).map(|value| !value),
        Proposition::And(left, right) => {
            match (proposition_value(left), proposition_value(right)) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            }
        }
        Proposition::Or(left, right) => match (proposition_value(left), proposition_value(right)) {
            (Some(true), _) | (_, Some(true)) => Some(true),
            (Some(false), Some(false)) => Some(false),
            _ => None,
        },
        Proposition::MemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => memory
            .intrinsic_access_in_bounds(pointer, *byte_width)
            .then_some(true),
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => {
            let format = if *wide {
                MachineIntegerType::UInt64
            } else {
                MachineIntegerType::UInt32
            };
            let (low, high) = bounds::machine_bounds(bytes, format)?;
            use num_traits::ToPrimitive;
            (low == high).then_some(())?;
            let bytes = low.to_u32()?;
            (bytes == 0 || memory.intrinsic_access_in_bounds(base, bytes)).then_some(true)
        }
        Proposition::MemoryReadDefined {
            memory,
            pointer,
            value_type,
        } => memory
            .directly_defined_read(pointer, *value_type)
            .then_some(true),
        Proposition::ResourceSeparate { left, right } => {
            intrinsic_separation(left, right).then_some(true)
        }
        Proposition::ResourceContains { parent, child } => {
            intrinsic_containment(parent, child).then_some(true)
        }
        Proposition::ConditionIs(condition, truth) => {
            condition_value(condition).map(|value| value == *truth)
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            algebraic_equality(left, right)
        }
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => integer_affine_comparison(
            &ConditionTerm::IntegerEqual(left.clone().into(), right.clone().into()),
        ),
        Proposition::Equal(left, right)
            if matches!(
                left,
                Term::Condition(_)
                    | Term::Bitvector32(_)
                    | Term::PointerOffset(_)
                    | Term::ProgramValue(_)
                    | Term::Sequence(_)
            ) && left == right =>
        {
            Some(true)
        }
        _ => None,
    }
}

fn condition_value(condition: &ConditionTerm) -> Option<bool> {
    match condition {
        ConditionTerm::Constant(value) => Some(*value),
        ConditionTerm::IntegerEqual(..)
        | ConditionTerm::IntegerNotEqual(..)
        | ConditionTerm::IntegerLessThan(..)
        | ConditionTerm::IntegerLessEqual(..)
        | ConditionTerm::IntegerGreaterThan(..)
        | ConditionTerm::IntegerGreaterEqual(..) => {
            let (left, right) = match condition {
                ConditionTerm::IntegerEqual(left, right)
                | ConditionTerm::IntegerNotEqual(left, right)
                | ConditionTerm::IntegerLessThan(left, right)
                | ConditionTerm::IntegerLessEqual(left, right)
                | ConditionTerm::IntegerGreaterThan(left, right)
                | ConditionTerm::IntegerGreaterEqual(left, right) => (left, right),
                _ => unreachable!(),
            };
            if left == right {
                return Some(matches!(
                    condition,
                    ConditionTerm::IntegerEqual(..)
                        | ConditionTerm::IntegerLessEqual(..)
                        | ConditionTerm::IntegerGreaterEqual(..)
                ));
            }
            super::super::integer_arithmetic::literal_integer_comparison_value(condition)
                .or_else(|| integer_affine_comparison(condition))
                .or_else(|| bounds::comparison(condition))
        }
        ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } => {
            if left == right {
                return Some(matches!(
                    relation,
                    CompareRelation::Equal
                        | CompareRelation::LessEqual
                        | CompareRelation::GreaterEqual
                ));
            }
            if let (Some(left), Some(right)) = (
                format.constant_from_term(left),
                format.constant_from_term(right),
            ) {
                let (left, right) = (left.to_integer(), right.to_integer());
                return Some(match relation {
                    CompareRelation::Equal => left == right,
                    CompareRelation::LessThan => left < right,
                    CompareRelation::LessEqual => left <= right,
                    CompareRelation::GreaterThan => left > right,
                    CompareRelation::GreaterEqual => left >= right,
                });
            }
            // Raw goal atoms retain their exact typed state identities.
            // In particular, this key must never canonicalize a memory read.
            machine_affine_equality(condition, Clone::clone)
                .or_else(|| bounds::comparison(condition))
        }
        ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
        ConditionTerm::PointerValueEqual(left, right) if left == right => Some(true),
        ConditionTerm::PointerOffsetEqual(left, right) if left == right => Some(true),
        ConditionTerm::AlgebraicEqual(left, right) => algebraic_equality(left, right),
        ConditionTerm::BoolEqual(left, right) if left == right => Some(true),
        // Float comparisons deliberately have no reflexivity rule: NaNs
        // compare unequal even when both operands have the same identity.
        _ => None,
    }
}

mod bounds;

fn byte_interval(range: &MemoryRange) -> Option<(i128, i128)> {
    let (start, end) = if let Some((start, end)) = range.wide_bounds() {
        (
            i128::from(start.uint64_as_const()?),
            i128::from(end.uint64_as_const()?),
        )
    } else {
        (
            i128::from(range.signed_constant_start()?),
            i128::from(range.signed_constant_end()?),
        )
    };
    if end < start {
        return None;
    }
    let width = i128::from(range.element_width());
    Some((start * width, end * width))
}

/// Remove only literal displacements from the explicit pointer syntax. The
/// symbolic address stays opaque: no aliases or memory reads are resolved.
fn offset_root(offset: &PointerOffsetTerm) -> (Option<&PointerOffsetTerm>, i128) {
    crate::instrumentation::record_deterministic_work(1);
    match offset {
        PointerOffsetTerm::Constant(value) => (None, i128::from(*value)),
        PointerOffsetTerm::Add(a, b) => {
            let a = offset_root(a);
            let b = offset_root(b);
            match (a.0, b.0) {
                (None, root) | (root, None) => (root, a.1 + b.1),
                _ => (Some(offset), 0),
            }
        }
        _ => (Some(offset), 0),
    }
}
fn pointer_delta(left: &Pointer, right: &Pointer) -> Option<i128> {
    if left.block != right.block {
        return None;
    }
    let left = offset_root(&left.offset);
    let right = offset_root(&right.offset);
    (left.0 == right.0).then_some(left.1 - right.1)
}

fn intrinsic_separation(left: &Resource, right: &Resource) -> bool {
    let (Resource::Memory(left), Resource::Memory(right)) = (left, right) else {
        return false;
    };
    if left.base().blocks_proven_distinct(right.base()) {
        return true;
    }
    let (Some((ls, le)), Some((rs, re))) = (byte_interval(left), byte_interval(right)) else {
        return false;
    };
    if ls == le || rs == re {
        return true;
    }
    pointer_delta(left.base(), right.base())
        .is_some_and(|delta| le + delta <= rs || re <= ls + delta)
}

fn intrinsic_containment(parent: &Resource, child: &Resource) -> bool {
    if parent == child {
        return true;
    }
    let (Resource::Memory(parent), Resource::Memory(child)) = (parent, child) else {
        return false;
    };
    let (Some((ps, pe)), Some((cs, ce))) = (byte_interval(parent), byte_interval(child)) else {
        return false;
    };
    cs == ce
        || pointer_delta(child.base(), parent.base())
            .is_some_and(|delta| ps <= cs + delta && ce + delta <= pe)
}

fn algebraic_equality(left: &AlgebraicTerm, right: &AlgebraicTerm) -> Option<bool> {
    if left.algebraic_type != right.algebraic_type {
        return None;
    }
    if left == right {
        return Some(true);
    }
    match (&left.node, &right.node) {
        (
            AlgebraicTermNode::Constructor { variant: left, .. },
            AlgebraicTermNode::Constructor { variant: right, .. },
        ) if left != right => Some(false),
        _ => None,
    }
}

/// Decide a C machine equality whose sides are sums and differences, at
/// either width, by their affine forms over `Z/2^width`. Each side flattens
/// into signed atoms and a constant; the two are equal exactly when every
/// atom cancels and the constants agree, and differ in every model when
/// every atom cancels and the constants do not. The identities used --
/// reordering, regrouping, and cancellation -- hold for exact and for
/// wrapping arithmetic alike, so a C signed overflow, which is a separate
/// definedness obligation, does not affect the verdict. Atoms are keyed by
/// the caller-selected key; anything else, including a product, is an atom.
/// The walk visits each node of the goal once.
pub(super) fn machine_affine_equality(
    condition: &ConditionTerm,
    atom_key: fn(&MachineTerm) -> MachineTerm,
) -> Option<bool> {
    let (left, right, wide) = match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } => (left, right, false),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => (left, right, true),
        _ => return None,
    };
    let mask = if wide { u64::MAX } else { u64::from(u32::MAX) };
    let mut atoms = std::collections::BTreeMap::new();
    let mut constant = 0u64;
    collect_machine_affine_atoms(left, 1, wide, &mut atoms, &mut constant, atom_key);
    collect_machine_affine_atoms(right, u64::MAX, wide, &mut atoms, &mut constant, atom_key);
    atoms
        .values()
        .all(|coefficient| coefficient & mask == 0)
        .then_some(constant & mask == 0)
}

fn collect_machine_affine_atoms(
    term: &MachineTerm,
    coefficient: u64,
    wide: bool,
    atoms: &mut std::collections::BTreeMap<MachineTerm, u64>,
    constant: &mut u64,
    atom_key: fn(&MachineTerm) -> MachineTerm,
) {
    crate::instrumentation::record_deterministic_work(1);
    match (term, wide) {
        (binary_term!(Int32, Add, left, right), false)
        | (
            MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Add,
                left,
                right,
            },
            true,
        )
        | (
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left,
                right,
            },
            true,
        ) => {
            collect_machine_affine_atoms(left, coefficient, wide, atoms, constant, atom_key);
            collect_machine_affine_atoms(right, coefficient, wide, atoms, constant, atom_key);
        }
        (binary_term!(Int32, Subtract, left, right), false)
        | (
            MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Subtract,
                left,
                right,
            },
            true,
        )
        | (
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Subtract,
                left,
                right,
            },
            true,
        ) => {
            collect_machine_affine_atoms(left, coefficient, wide, atoms, constant, atom_key);
            collect_machine_affine_atoms(
                right,
                coefficient.wrapping_neg(),
                wide,
                atoms,
                constant,
                atom_key,
            );
        }
        (int32_constant!(value), false) => {
            *constant =
                constant.wrapping_add(coefficient.wrapping_mul(u64::from(constant_u32(*value))));
        }
        (int64_constant!(value), true) => {
            *constant =
                constant.wrapping_add(coefficient.wrapping_mul(constant_i64(*value) as u64));
        }
        (uint64_constant!(value), true) => {
            *constant = constant.wrapping_add(coefficient.wrapping_mul(constant_u64(*value)));
        }
        (atom, _) => {
            let entry = atoms.entry(atom_key(atom)).or_insert(0);
            *entry = entry.wrapping_add(coefficient);
        }
    }
}

/// The exact `Integer` counterpart of [`machine_affine_equality`]: sums,
/// differences, and negations flatten into signed atoms and a constant over
/// the integers, with no modulus. When every atom cancels, the sides differ
/// by that constant, which decides equality and, because `Integer` has no
/// overflow, order as well. Atoms are interned terms, keyed by their shared
/// identity. The walk visits each node of the goal once.
pub(super) fn integer_affine_comparison(condition: &ConditionTerm) -> Option<bool> {
    use num_traits::Zero;
    let (left, right) = match condition {
        ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right)
        | ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right) => (left, right),
        _ => return None,
    };
    let (atoms, difference) = integer_affine_difference(left, right);
    if atoms.values().any(|coefficient| !coefficient.is_zero()) {
        return None;
    }
    let zero = num_bigint::BigInt::zero();
    Some(match condition {
        ConditionTerm::IntegerEqual(..) => difference == zero,
        ConditionTerm::IntegerNotEqual(..) => difference != zero,
        ConditionTerm::IntegerLessThan(..) => difference < zero,
        ConditionTerm::IntegerLessEqual(..) => difference <= zero,
        ConditionTerm::IntegerGreaterThan(..) => difference > zero,
        _ => difference >= zero,
    })
}

fn integer_product_identity(term: &IntegerTerm) -> Option<&SharedIntegerTerm> {
    use num_traits::{One, Zero};
    let IntegerTerm::Multiply(a, b) = term else {
        return None;
    };
    if matches!(a.as_ref(), IntegerTerm::Constant(n) if n.is_zero())
        || matches!(b.as_ref(), IntegerTerm::Constant(n) if n.is_one())
    {
        Some(a)
    } else if matches!(b.as_ref(), IntegerTerm::Constant(n) if n.is_zero())
        || matches!(a.as_ref(), IntegerTerm::Constant(n) if n.is_one())
    {
        Some(b)
    } else {
        None
    }
}

/// The affine form of `left - right`: each atom's coefficient and the
/// constant. Interned terms share subterms, so a sum such as
/// `a + a` over `a = b + b` reaches one node along many paths; coefficients
/// are propagated over the term DAG in topological order, visiting each node
/// once, rather than walking every path.
fn integer_affine_difference(
    left: &SharedIntegerTerm,
    right: &SharedIntegerTerm,
) -> (
    std::collections::BTreeMap<u64, num_bigint::BigInt>,
    num_bigint::BigInt,
) {
    use num_traits::Zero;
    // Postorder over the arithmetic nodes, so reversing it puts every node
    // before the operands it passes its coefficient to.
    let mut order = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![(left.clone(), false), (right.clone(), false)];
    while let Some((term, expanded)) = stack.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if expanded {
            order.push(term);
            continue;
        }
        if !seen.insert(term.id()) {
            continue;
        }
        stack.push((term.clone(), true));
        match term.as_ref() {
            IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right) => {
                stack.push((right.clone(), false));
                stack.push((left.clone(), false));
            }
            IntegerTerm::Negate(value) => stack.push((value.clone(), false)),
            other => {
                if let Some(value) = integer_product_identity(other) {
                    stack.push((value.clone(), false));
                }
            }
        }
    }
    let mut coefficients = std::collections::HashMap::<u64, num_bigint::BigInt>::new();
    *coefficients.entry(left.id()).or_default() += 1;
    *coefficients.entry(right.id()).or_default() -= 1;
    let mut atoms = std::collections::BTreeMap::new();
    let mut constant = num_bigint::BigInt::zero();
    for term in order.iter().rev() {
        crate::instrumentation::record_deterministic_work(1);
        let Some(coefficient) = coefficients.remove(&term.id()) else {
            continue;
        };
        if coefficient.is_zero() {
            continue;
        }
        match term.as_ref() {
            IntegerTerm::Add(left, right) => {
                *coefficients.entry(left.id()).or_default() += &coefficient;
                *coefficients.entry(right.id()).or_default() += &coefficient;
            }
            IntegerTerm::Subtract(left, right) => {
                *coefficients.entry(left.id()).or_default() += &coefficient;
                *coefficients.entry(right.id()).or_default() -= &coefficient;
            }
            IntegerTerm::Negate(value) => {
                *coefficients.entry(value.id()).or_default() -= &coefficient;
            }
            IntegerTerm::Constant(value) => constant += value * coefficient,
            other if integer_product_identity(other).is_some() => {
                let value = integer_product_identity(other).unwrap();
                *coefficients.entry(value.id()).or_default() += coefficient;
            }
            _ => {
                *atoms
                    .entry(term.id())
                    .or_insert_with(num_bigint::BigInt::zero) += coefficient;
            }
        }
    }
    (atoms, constant)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn computation_reads_constants_at_the_comparison_format() {
        for (format, expected) in [
            (MachineIntegerType::Int32, true),
            (MachineIntegerType::UInt32, false),
        ] {
            let condition = ConditionTerm::Compare {
                format,
                relation: CompareRelation::LessThan,
                left: Box::new(MachineTerm::constant(u32::MAX)),
                right: Box::new(MachineTerm::constant(0)),
            };
            assert!(computes_leaf(&Proposition::ConditionIs(
                condition.clone(),
                expected
            )));
            assert!(!computes_leaf(&Proposition::ConditionIs(
                condition, !expected
            )));
        }
    }

    #[test]
    fn computation_does_not_use_float_reflexivity() {
        let nan = MachineTerm::constant(0x7fc00000);
        let goal = Proposition::ConditionIs(
            ConditionTerm::Float32(FloatCondition::Comparison {
                operator: ComparisonOperator::Equal,
                left: Box::new(nan.clone()),
                right: Box::new(nan),
            }),
            true,
        );
        assert!(!computes_leaf(&goal));
    }
    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/kernel/proof/fact_reasoning/computation/tests.rs");
    }
}
