//! Explicit certificates for linear arithmetic over mathematical integers.
//!
//! A planner supplies a flat, topologically ordered certificate. Checking
//! validates only the referenced premises and local nodes; it does not invoke
//! the machine signed arithmetic checker or search ambient facts.

pub(crate) use super::integer_affine_atoms::IntegerAffineAtom;
use super::integer_affine_atoms::{IntegerFoldAtomRecord, intern_integer_fold_atom};
use crate::kernel::{ConditionTerm, IntegerTerm, Proposition};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

/// The normalized relation `sum(coeff * variable) + constant REL 0`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum IntegerAffineRelation {
    LessEqual,
    Equal,
}

/// A claimed local affine result. The checker recomputes this value at every
/// node, making changes to terms, coefficients, operators, or constants
/// visible to the certificate boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IntegerAffineClaim {
    pub(crate) relation: IntegerAffineRelation,
    pub(crate) terms: BTreeMap<IntegerAffineAtom, BigInt>,
    pub(crate) constant: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum IntegerArithmeticNode {
    Premise {
        index: usize,
        result: IntegerAffineClaim,
    },
    Scale {
        source: usize,
        coefficient: BigInt,
        result: IntegerAffineClaim,
    },
    Add {
        left: usize,
        right: usize,
        result: IntegerAffineClaim,
    },
    /// Turn an equality into one of its two non-strict directions.
    EqualityToLessEqual {
        source: usize,
        reverse: bool,
        result: IntegerAffineClaim,
    },
    /// Close an equality from opposite non-strict bounds.
    EqualityFromBounds {
        lower: usize,
        upper: usize,
        result: IntegerAffineClaim,
    },
    /// Context-free tautologies such as `x + 1 > x` and `x - x == 0`.
    Trivial { result: IntegerAffineClaim },
}

/// A flat, locally checkable linear arithmetic certificate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IntegerArithmeticCertificate {
    pub(crate) nodes: Vec<IntegerArithmeticNode>,
    pub(crate) conclusion: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IntegerArithmeticCheckError {
    InvalidPremise(usize),
    InvalidNodeReference(usize),
    UnsupportedPremise(usize),
    UnsupportedGoal,
    NodeResultMismatch(usize),
    InvalidCoefficient(usize),
    InvalidRelation(usize),
    WorkLimitExceeded,
    DoesNotFollow,
}

impl IntegerArithmeticCertificate {
    pub(crate) fn check(
        &self,
        goal: &Proposition,
        premises: &[Proposition],
    ) -> Result<(), IntegerArithmeticCheckError> {
        let mut collection_context = IntegerAffineCollectionContext::default();
        // Keep fold alpha keys scoped to this checked certificate. This
        // reuses one key for shared source nodes across the goal and all
        // explicitly selected premises without retaining a process-wide
        // source-id cache.
        let expected = integer_affine_claim_with_context(goal, &mut collection_context)
            .ok_or(IntegerArithmeticCheckError::UnsupportedGoal)?;
        let mut checked: Vec<IntegerAffineClaim> = Vec::with_capacity(self.nodes.len());
        // A premise can be referenced by many nodes. Cache by its explicit
        // index so a large expression is normalized once per check.
        #[derive(Clone)]
        enum CachedPremise {
            Unknown,
            Supported(IntegerAffineClaim),
            Unsupported,
        }
        let mut premise_cache = vec![CachedPremise::Unknown; premises.len()];
        for (node_index, node) in self.nodes.iter().enumerate() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
            }
            let result = match node {
                IntegerArithmeticNode::Premise { index, result } => {
                    let premise = premises
                        .get(*index)
                        .ok_or(IntegerArithmeticCheckError::InvalidPremise(*index))?;
                    if matches!(premise_cache[*index], CachedPremise::Unknown) {
                        let Some(expected) =
                            integer_affine_claim_with_context(premise, &mut collection_context)
                        else {
                            premise_cache[*index] = CachedPremise::Unsupported;
                            return Err(IntegerArithmeticCheckError::UnsupportedPremise(*index));
                        };
                        premise_cache[*index] = CachedPremise::Supported(expected);
                    }
                    let expected = match &premise_cache[*index] {
                        CachedPremise::Supported(expected) => expected,
                        CachedPremise::Unsupported => {
                            return Err(IntegerArithmeticCheckError::UnsupportedPremise(*index));
                        }
                        CachedPremise::Unknown => unreachable!(),
                    };
                    if !charge_claim_work(expected) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    if expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected.clone()
                }
                IntegerArithmeticNode::Scale {
                    source,
                    coefficient,
                    result,
                } => {
                    let source = checked
                        .get(*source)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*source))?;
                    if matches!(source.relation, IntegerAffineRelation::LessEqual)
                        && coefficient < &BigInt::zero()
                    {
                        return Err(IntegerArithmeticCheckError::InvalidCoefficient(node_index));
                    }
                    let expected = scale_claim(source, coefficient)
                        .ok_or(IntegerArithmeticCheckError::WorkLimitExceeded)?;
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::Add {
                    left,
                    right,
                    result,
                } => {
                    let left = checked
                        .get(*left)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*left))?;
                    let right = checked
                        .get(*right)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*right))?;
                    if left.relation != right.relation {
                        return Err(IntegerArithmeticCheckError::InvalidRelation(node_index));
                    }
                    if !charge_claim_work(left) || !charge_claim_work(right) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let expected = add_claim(left, right);
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::EqualityToLessEqual {
                    source,
                    reverse,
                    result,
                } => {
                    let source = checked
                        .get(*source)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*source))?;
                    if source.relation != IntegerAffineRelation::Equal {
                        return Err(IntegerArithmeticCheckError::InvalidRelation(node_index));
                    }
                    if !charge_claim_work(source) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let expected = if *reverse {
                        negate_claim(source, IntegerAffineRelation::LessEqual)
                    } else {
                        IntegerAffineClaim {
                            relation: IntegerAffineRelation::LessEqual,
                            terms: source.terms.clone(),
                            constant: source.constant.clone(),
                        }
                    };
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => {
                    let lower = checked
                        .get(*lower)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*lower))?;
                    let upper = checked
                        .get(*upper)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*upper))?;
                    if lower.relation != IntegerAffineRelation::LessEqual
                        || upper.relation != IntegerAffineRelation::LessEqual
                    {
                        return Err(IntegerArithmeticCheckError::InvalidRelation(node_index));
                    }
                    if !charge_claim_work(lower) || !charge_claim_work(upper) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let expected = IntegerAffineClaim {
                        relation: IntegerAffineRelation::Equal,
                        terms: lower.terms.clone(),
                        constant: lower.constant.clone(),
                    };
                    if !claims_are_opposites(lower, upper) || &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::Trivial { result } => {
                    if !charge_claim_work(result) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    if !claim_is_trivial(result) {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    result.clone()
                }
            };
            if !charge_claim_work(&result) {
                return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
            }
            checked.push(result);
        }
        let actual = checked.get(self.conclusion).ok_or(
            IntegerArithmeticCheckError::InvalidNodeReference(self.conclusion),
        )?;
        if !charge_claim_work(actual) || !charge_claim_work(&expected) {
            return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
        }
        (actual == &expected)
            .then_some(())
            .ok_or(IntegerArithmeticCheckError::DoesNotFollow)
    }
}

fn charge_claim_work(claim: &IntegerAffineClaim) -> bool {
    let mut bits = claim.constant.bits() as usize;
    for coefficient in claim.terms.values() {
        bits = bits.saturating_add(1 + coefficient.bits() as usize);
    }
    !crate::instrumentation::deadline_exceeded_with_work(
        bits.saturating_add(claim.terms.len()).max(1),
    )
}

fn charge_integer_product(left: &BigInt, right: &BigInt) -> bool {
    let units = (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1);
    if crate::instrumentation::deadline_exceeded_with_work(units) {
        return false;
    }
    true
}

fn scale_claim(claim: &IntegerAffineClaim, coefficient: &BigInt) -> Option<IntegerAffineClaim> {
    let mut terms = Vec::with_capacity(claim.terms.len());
    for (term, value) in &claim.terms {
        if !charge_integer_product(value, coefficient) {
            return None;
        }
        let value = value * coefficient;
        if !value.is_zero() {
            terms.push((term.clone(), value));
        }
    }
    if !charge_integer_product(&claim.constant, coefficient) {
        return None;
    }
    Some(IntegerAffineClaim {
        relation: claim.relation.clone(),
        terms: terms.into_iter().collect(),
        constant: &claim.constant * coefficient,
    })
}

fn add_claim(left: &IntegerAffineClaim, right: &IntegerAffineClaim) -> IntegerAffineClaim {
    let mut terms = left.terms.clone();
    for (term, coefficient) in &right.terms {
        let value = terms.get(term).cloned().unwrap_or_else(BigInt::zero) + coefficient;
        if value.is_zero() {
            terms.remove(term);
        } else {
            terms.insert(term.clone(), value);
        }
    }
    IntegerAffineClaim {
        relation: left.relation.clone(),
        terms,
        constant: &left.constant + &right.constant,
    }
}

fn negate_claim(claim: &IntegerAffineClaim, relation: IntegerAffineRelation) -> IntegerAffineClaim {
    let terms = claim
        .terms
        .iter()
        .map(|(term, coefficient)| (term.clone(), -coefficient))
        .filter(|(_, coefficient)| !coefficient.is_zero())
        .collect();
    IntegerAffineClaim {
        relation,
        terms,
        constant: -&claim.constant,
    }
}

fn claims_are_opposites(lower: &IntegerAffineClaim, upper: &IntegerAffineClaim) -> bool {
    lower.terms.len() == upper.terms.len()
        && lower
            .terms
            .iter()
            .zip(&upper.terms)
            .all(|((left, a), (right, b))| left == right && -a == *b)
        && -&lower.constant == upper.constant
}

fn claim_is_trivial(claim: &IntegerAffineClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            IntegerAffineRelation::LessEqual => claim.constant <= BigInt::zero(),
            IntegerAffineRelation::Equal => claim.constant.is_zero(),
        }
}

/// Per-claim cache for fold identities.  This is deliberately scoped to one
/// normalization: a shared source node is never alpha-keyed once for each
/// occurrence in the same claim, while load-registry epochs cannot make a
/// process-wide source-id cache stale.
#[derive(Default)]
struct IntegerAffineCollectionContext {
    fold_atoms: HashMap<crate::kernel::SharedIntegerTerm, Arc<IntegerFoldAtomRecord>>,
}

#[cfg(test)]
thread_local! {
    static INTEGER_FOLD_ALPHA_CONSTRUCTIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
fn reset_fold_alpha_constructions() {
    INTEGER_FOLD_ALPHA_CONSTRUCTIONS.with(|count| count.set(0));
}

#[cfg(test)]
fn fold_alpha_constructions() -> usize {
    INTEGER_FOLD_ALPHA_CONSTRUCTIONS.with(std::cell::Cell::get)
}

fn fold_atom_for_claim(
    context: &mut IntegerAffineCollectionContext,
    term: &crate::kernel::SharedIntegerTerm,
) -> Option<Arc<IntegerFoldAtomRecord>> {
    if let Some(atom) = context.fold_atoms.get(term) {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        return Some(atom.clone());
    }
    #[cfg(test)]
    INTEGER_FOLD_ALPHA_CONSTRUCTIONS.with(|count| count.set(count.get() + 1));
    let atom = intern_integer_fold_atom(term)?;
    context.fold_atoms.insert(term.clone(), atom.clone());
    Some(atom)
}

/// Normalize one integer proposition for use in a certificate node.
///
/// This is intentionally a small, context-free conversion. The returned
/// atom map contains only checked source identities: variables, machine
/// observations, pure applications, and snapshot-aware opaque folds. An
/// arbitrary deep Integer term is never used directly as a map key.
pub(crate) fn integer_affine_claim(proposition: &Proposition) -> Option<IntegerAffineClaim> {
    let mut context = IntegerAffineCollectionContext::default();
    integer_affine_claim_with_context(proposition, &mut context)
}

fn integer_affine_claim_with_context(
    proposition: &Proposition,
    context: &mut IntegerAffineCollectionContext,
) -> Option<IntegerAffineClaim> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return None,
        },
        _ => return None,
    };
    if let ConditionTerm::Constant(actual) = condition {
        return Some(IntegerAffineClaim {
            relation: IntegerAffineRelation::Equal,
            terms: BTreeMap::new(),
            constant: if *actual == value {
                BigInt::zero()
            } else {
                BigInt::one()
            },
        });
    }
    let (left, right, relation, strict) = match condition {
        ConditionTerm::IntegerLessThan(left, right) if value => {
            (left, right, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerLessEqual(left, right) if value => {
            (left, right, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerGreaterThan(left, right) if value => {
            (right, left, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) if value => {
            (right, left, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerEqual(left, right) if value => {
            (left, right, IntegerAffineRelation::Equal, false)
        }
        ConditionTerm::IntegerLessThan(left, right) => {
            (right, left, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            (right, left, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            (left, right, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            (left, right, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerEqual(left, right) => {
            // Disequality is outside this fragment, except for constants.
            let mut terms = BTreeMap::new();
            let mut constant = BigInt::zero();
            collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
            collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                context,
            )?;
            return (terms.is_empty() && !constant.is_zero()).then_some(IntegerAffineClaim {
                relation: IntegerAffineRelation::LessEqual,
                terms,
                constant: BigInt::from(-1),
            });
        }
        ConditionTerm::IntegerNotEqual(left, right) if value => {
            let mut terms = BTreeMap::new();
            let mut constant = BigInt::zero();
            collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
            collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                context,
            )?;
            return (terms.is_empty() && !constant.is_zero()).then_some(IntegerAffineClaim {
                relation: IntegerAffineRelation::LessEqual,
                terms,
                constant: BigInt::from(-1),
            });
        }
        ConditionTerm::IntegerNotEqual(left, right) => {
            let mut terms = BTreeMap::new();
            let mut constant = BigInt::zero();
            collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
            collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                context,
            )?;
            return (terms.is_empty() && constant.is_zero()).then_some(IntegerAffineClaim {
                relation: IntegerAffineRelation::Equal,
                terms,
                constant,
            });
        }
        _ => return None,
    };
    let mut terms = BTreeMap::new();
    let mut constant = BigInt::zero();
    collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
    collect_integer_affine_terms(right, &BigInt::from(-1), &mut terms, &mut constant, context)?;
    if strict {
        if crate::instrumentation::deadline_exceeded_with_work(constant.bits() as usize + 1) {
            return None;
        }
        constant += BigInt::one();
    }
    Some(IntegerAffineClaim {
        relation,
        terms,
        constant,
    })
}

fn collect_integer_affine_terms(
    term: &crate::kernel::SharedIntegerTerm,
    coefficient: &BigInt,
    terms: &mut BTreeMap<IntegerAffineAtom, BigInt>,
    constant: &mut BigInt,
    context: &mut IntegerAffineCollectionContext,
) -> Option<()> {
    // First collect the reachable DAG in postorder.  The interner gives each
    // node a stable identity, so this schedules a shared node exactly once.
    let mut scheduled = HashSet::new();
    let mut stack = vec![(term.clone(), false)];
    let mut order = Vec::new();
    while let Some((node, expanded)) = stack.pop() {
        if expanded {
            order.push(node);
            continue;
        }
        if !scheduled.insert(node.id()) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        stack.push((node.clone(), true));
        match node.as_ref() {
            IntegerTerm::Negate(child) => stack.push((child.clone(), false)),
            IntegerTerm::Add(left, right)
            | IntegerTerm::Subtract(left, right)
            | IntegerTerm::Multiply(left, right) => {
                stack.push((right.clone(), false));
                stack.push((left.clone(), false));
            }
            IntegerTerm::Constant(_)
            | IntegerTerm::Variable(_)
            | IntegerTerm::Machine(_)
            | IntegerTerm::PureFunctionApplication(_)
            | IntegerTerm::AlgebraicMatch { .. } => {}
            // A RangeFold is a checked opaque atom.  Its body and endpoints
            // are represented by the kernel-issued alpha key below; affine
            // normalization must never enumerate or lower the range here.
            IntegerTerm::RangeFold { .. } => {}
        }
    }

    // Propagate the coefficient from each root toward the leaves.  This
    // keeps only one scalar per reachable node; no internal node constructs
    // or clones a complete affine map.
    let mut weights = HashMap::new();
    weights.insert(term.id(), coefficient.clone());
    for node in order.into_iter().rev() {
        let Some(weight) = weights.remove(&node.id()) else {
            continue;
        };
        if crate::instrumentation::deadline_exceeded_with_work(weight.bits() as usize + 1) {
            return None;
        }
        if weight.is_zero() {
            continue;
        }
        match node.as_ref() {
            IntegerTerm::Constant(value) => {
                if !charge_integer_product(&weight, value) {
                    return None;
                }
                if crate::instrumentation::deadline_exceeded_with_work(
                    weight.bits() as usize + value.bits() as usize + 1,
                ) {
                    return None;
                }
                *constant += &weight * value;
            }
            IntegerTerm::Variable(_)
            | IntegerTerm::Machine(_)
            | IntegerTerm::PureFunctionApplication(_)
            | IntegerTerm::AlgebraicMatch { .. } => {
                let atom = match node.as_ref() {
                    IntegerTerm::Variable(variable) => IntegerAffineAtom::Variable(*variable),
                    IntegerTerm::Machine(source) => IntegerAffineAtom::Machine(source.id()),
                    IntegerTerm::AlgebraicMatch { .. } => return None,
                    IntegerTerm::PureFunctionApplication(application) => {
                        IntegerAffineAtom::Application(application.id())
                    }
                    _ => unreachable!(),
                };
                let existing = terms.get(&atom).map_or(0, |value| value.bits() as usize);
                if crate::instrumentation::deadline_exceeded_with_work(
                    existing + weight.bits() as usize + 1,
                ) {
                    return None;
                }
                let merged = terms.remove(&atom).unwrap_or_else(BigInt::zero) + weight;
                if !merged.is_zero() {
                    terms.insert(atom, merged);
                }
            }
            IntegerTerm::RangeFold { .. } => {
                let atom = IntegerAffineAtom::Fold(fold_atom_for_claim(context, &node)?);
                let existing = terms.get(&atom).map_or(0, |value| value.bits() as usize);
                if crate::instrumentation::deadline_exceeded_with_work(
                    existing + weight.bits() as usize + 1,
                ) {
                    return None;
                }
                let merged = terms.remove(&atom).unwrap_or_else(BigInt::zero) + weight;
                if !merged.is_zero() {
                    terms.insert(atom, merged);
                }
            }
            IntegerTerm::Negate(child) => {
                if !add_weight(&mut weights, child.id(), -weight) {
                    return None;
                }
            }
            IntegerTerm::Add(left, right) => {
                if !add_weight(&mut weights, left.id(), weight.clone())
                    || !add_weight(&mut weights, right.id(), weight)
                {
                    return None;
                }
            }
            IntegerTerm::Subtract(left, right) => {
                if !add_weight(&mut weights, left.id(), weight.clone())
                    || !add_weight(&mut weights, right.id(), -weight)
                {
                    return None;
                }
            }
            IntegerTerm::Multiply(left, right) => {
                let (child, factor) = if let Some(value) = left.as_const() {
                    (right, value)
                } else {
                    let value = right.as_const()?;
                    (left, value)
                };
                if !charge_integer_product(&weight, factor) {
                    return None;
                }
                if !add_weight(&mut weights, child.id(), weight * factor) {
                    return None;
                }
            }
        }
    }
    Some(())
}

fn add_weight(weights: &mut HashMap<u64, BigInt>, id: u64, weight: BigInt) -> bool {
    let existing = weights.get(&id).map_or(0, |value| value.bits() as usize);
    if crate::instrumentation::deadline_exceeded_with_work(existing + weight.bits() as usize + 1) {
        return false;
    }
    let merged = weights.remove(&id).unwrap_or_else(BigInt::zero) + weight;
    if !merged.is_zero() {
        weights.insert(id, merged);
    }
    true
}

#[cfg(test)]
mod tests {
    use crate::kernel::Variable;

    use super::*;

    #[test]
    fn integer_affine_dag_scaling_includes_distinct_variables_and_shared_paths() {
        let mut distinct_work = Vec::new();
        let mut shared_work = Vec::new();
        for size in [8usize, 16, 32, 64] {
            let mut distinct = IntegerTerm::var(Variable(10_000));
            let mut shared = IntegerTerm::var(Variable(20_000));
            for index in 1..size {
                distinct =
                    IntegerTerm::add(distinct, IntegerTerm::var(Variable(10_000 + index as u64)));
            }
            for _ in 0..size {
                shared = IntegerTerm::add(shared.clone(), shared.clone());
            }
            for (expression, measurements, is_shared) in [
                (distinct, &mut distinct_work, false),
                (shared, &mut shared_work, true),
            ] {
                let goal = proposition(ConditionTerm::integer_less_equal(
                    expression,
                    IntegerTerm::constant_i64(0),
                ));
                let (result, work) =
                    crate::instrumentation::measure_deterministic_work(|| claim(&goal));
                if is_shared {
                    assert_eq!(
                        result.terms,
                        BTreeMap::from([(
                            IntegerAffineAtom::Variable(Variable(20_000)),
                            BigInt::one() << size
                        )])
                    );
                } else {
                    assert_eq!(result.terms.len(), size);
                    assert!(
                        result
                            .terms
                            .values()
                            .all(|coefficient| coefficient == &BigInt::one())
                    );
                }
                measurements.push(work);
            }
        }
        for pair in distinct_work.windows(2) {
            assert!(pair[1] <= 3 * pair[0], "{distinct_work:?}");
        }
        for pair in shared_work.windows(2) {
            assert!(
                pair[1] <= 5 * pair[0],
                "growing coefficient bit lengths: {shared_work:?}"
            );
        }
    }

    #[test]
    fn integer_affine_graph_collection_stops_at_the_active_budget() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};
        let mut expression = IntegerTerm::var(Variable(30_000));
        for _ in 0..64 {
            expression = IntegerTerm::add(expression.clone(), expression.clone());
        }
        let goal = proposition(ConditionTerm::integer_less_equal(
            expression,
            IntegerTerm::constant_i64(0),
        ));
        instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: 16,
                smart: 16,
                control: 16,
            },
            || {
                let tactic = TacticEvent {
                    claim: "integer budget".into(),
                    tactic_index: 0,
                    tactic_name: "integer_certificate".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                assert!(integer_affine_claim(&goal).is_none());
                instrumentation::emit(VerificationEvent::TacticFailed(tactic));
            },
        );
    }

    fn variable(id: u64) -> IntegerTerm {
        IntegerTerm::Variable(Variable(id))
    }

    fn proposition(condition: ConditionTerm) -> Proposition {
        Proposition::ConditionIs(condition, true)
    }

    fn claim(proposition: &Proposition) -> IntegerAffineClaim {
        integer_affine_claim(proposition).expect("integer proposition should be affine")
    }

    fn premise(index: usize, proposition: &Proposition) -> IntegerArithmeticNode {
        IntegerArithmeticNode::Premise {
            index,
            result: claim(proposition),
        }
    }

    #[test]
    fn machine_observations_are_sorted_opaque_affine_atoms() {
        use crate::kernel::{Bitvector32Term, MachineIntegerType};
        let observe = |ty, bits| IntegerTerm::from_machine(ty, bits).unwrap();
        let bits = Bitvector32Term::Variable(Variable(490));
        let x = observe(MachineIntegerType::Int32, bits.clone());
        let same = observe(MachineIntegerType::Int32, bits.clone());
        let unsigned = observe(MachineIntegerType::UInt32, bits.clone());
        let goal = proposition(ConditionTerm::integer_equal(
            IntegerTerm::subtract(IntegerTerm::add(x.clone(), variable(491)), same),
            variable(491),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: claim(&goal),
            }],
            conclusion: 0,
        };
        assert!(certificate.check(&goal, &[]).is_ok());
        let wrong_signedness = proposition(ConditionTerm::integer_equal(x.clone(), unsigned));
        assert!(certificate.check(&wrong_signedness, &[]).is_err());

        let y_bits = Bitvector32Term::Variable(Variable(492));
        let y = observe(MachineIntegerType::Int32, y_bits.clone());
        let machine_sum = observe(
            MachineIntegerType::Int32,
            Bitvector32Term::Add(Box::new(bits), Box::new(y_bits)),
        );
        let unchecked_distribution = proposition(ConditionTerm::integer_equal(
            machine_sum,
            IntegerTerm::add(x, y),
        ));
        let forged = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: claim(&unchecked_distribution),
            }],
            conclusion: 0,
        };
        assert!(forged.check(&unchecked_distribution, &[]).is_err());
    }

    fn int32_fold(
        start: u32,
        end: u32,
        accumulator: u64,
        item: u64,
        body: IntegerTerm,
    ) -> IntegerTerm {
        use crate::kernel::{IntegerRangeFoldIndex, SharedIntegerRangeEndpoint};
        IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(
                    crate::kernel::Bitvector32Term::Constant(start),
                ),
                end: SharedIntegerRangeEndpoint::intern(crate::kernel::Bitvector32Term::Constant(
                    end,
                )),
            },
            IntegerTerm::constant_i64(0),
            Variable(accumulator),
            Variable(item),
            body,
        )
    }

    fn integer_fold(
        start: i64,
        end: i64,
        accumulator: u64,
        item: u64,
        body: IntegerTerm,
    ) -> IntegerTerm {
        use crate::kernel::IntegerRangeFoldIndex;
        IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(start).into(),
                end: IntegerTerm::constant_i64(end).into(),
            },
            IntegerTerm::constant_i64(0),
            Variable(accumulator),
            Variable(item),
            body,
        )
    }

    fn fold_body(accumulator: u64, item: u64) -> IntegerTerm {
        IntegerTerm::add(
            IntegerTerm::var(Variable(accumulator)),
            IntegerTerm::var(Variable(item)),
        )
    }

    fn machine_item(item: u64) -> IntegerTerm {
        IntegerTerm::from_machine(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::Bitvector32Term::Variable(Variable(item)),
        )
        .expect("a symbolic Int32 item should be a machine observation")
    }

    fn machine_fold_body(accumulator: u64, item: u64) -> IntegerTerm {
        IntegerTerm::add(IntegerTerm::var(Variable(accumulator)), machine_item(item))
    }

    #[test]
    fn alpha_renamed_folds_cancel_as_one_checked_affine_atom() {
        let left = int32_fold(0, 8, 100, 101, machine_fold_body(100, 101));
        let right = int32_fold(0, 8, 200, 201, machine_fold_body(200, 201));
        let goal = proposition(ConditionTerm::IntegerEqual(left.into(), right.into()));
        let normalized = claim(&goal);
        assert!(normalized.terms.is_empty());
        assert!(normalized.constant.is_zero());

        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial { result: normalized }],
            conclusion: 0,
        };
        certificate.check(&goal, &[]).unwrap();
    }

    #[test]
    fn fold_atom_identity_keeps_endpoints_body_and_carrier_distinct() {
        let baseline = int32_fold(0, 8, 300, 301, machine_fold_body(300, 301));
        let changed_end = int32_fold(0, 9, 300, 301, machine_fold_body(300, 301));
        let changed_body = int32_fold(
            0,
            8,
            300,
            301,
            IntegerTerm::subtract(IntegerTerm::var(Variable(300)), machine_item(301)),
        );
        let changed_carrier = integer_fold(0, 8, 300, 301, fold_body(300, 301));

        for other in [changed_end, changed_body, changed_carrier] {
            let goal = proposition(ConditionTerm::IntegerEqual(
                baseline.clone().into(),
                other.into(),
            ));
            assert_eq!(claim(&goal).terms.len(), 2);
        }
    }

    #[test]
    fn fold_atom_tampering_is_rejected_at_the_certificate_boundary() {
        let source_fold = int32_fold(0, 8, 400, 401, machine_fold_body(400, 401));
        let changed_fold = int32_fold(0, 9, 400, 401, machine_fold_body(400, 401));
        let source = proposition(ConditionTerm::IntegerLessEqual(
            source_fold.into(),
            IntegerTerm::constant_i64(0).into(),
        ));
        let forged = proposition(ConditionTerm::IntegerLessEqual(
            changed_fold.into(),
            IntegerTerm::constant_i64(0).into(),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Premise {
                index: 0,
                result: claim(&forged),
            }],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&source, std::slice::from_ref(&source)),
            Err(IntegerArithmeticCheckError::NodeResultMismatch(0))
        );
    }

    #[test]
    fn fold_atom_identity_retains_the_exact_memory_snapshot() {
        use crate::kernel::{
            Bitvector32Term, CMemory, CValue, IntegerRangeFoldIndex, MachineIntegerType, Pointer,
            PointerOffsetTerm, SharedIntegerRangeEndpoint, SharedMachineIntegerTerm,
        };
        let pointer = Pointer {
            block: "affine-fold-snapshot".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before =
            crate::kernel::intern_c_memory(CMemory::new().with_block("affine-fold-snapshot", 8));
        let after = crate::kernel::intern_c_memory(
            before
                .as_ref()
                .clone()
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
        );
        let load_fold =
            |memory: &crate::kernel::SharedCMemory, accumulator: u64, item: u64| -> IntegerTerm {
                IntegerTerm::range_fold(
                    IntegerRangeFoldIndex::Int32 {
                        start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
                        end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(2)),
                    },
                    IntegerTerm::constant_i64(0),
                    Variable(accumulator),
                    Variable(item),
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        Bitvector32Term::MemoryLoad(memory.clone(), Box::new(pointer.clone())),
                    )),
                )
            };
        let before_fold = load_fold(&before, 700, 701);
        let renamed_before_fold = load_fold(&before, 800, 801);
        let after_fold = load_fold(&after, 800, 801);

        let renamed_goal = proposition(ConditionTerm::IntegerEqual(
            before_fold.clone().into(),
            renamed_before_fold.into(),
        ));
        assert!(claim(&renamed_goal).terms.is_empty());

        let changed_snapshot_goal = proposition(ConditionTerm::IntegerEqual(
            before_fold.into(),
            after_fold.into(),
        ));
        assert_eq!(claim(&changed_snapshot_goal).terms.len(), 2);
    }

    #[test]
    fn repeated_fold_atoms_share_scoped_alpha_work() {
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let item = Variable(500 + depth as u64);
            let accumulator = Variable(600 + depth as u64);
            let mut body = machine_fold_body(accumulator.0, item.0);
            for _ in 0..depth {
                let shared: crate::kernel::SharedIntegerTerm = body.clone().into();
                body = IntegerTerm::add(body, shared.as_ref().clone());
            }
            let fold = int32_fold(0, 8, accumulator.0, item.0, body);
            let expression = IntegerTerm::add(fold.clone(), fold);
            let goal = proposition(ConditionTerm::IntegerEqual(
                expression.into(),
                IntegerTerm::constant_i64(0).into(),
            ));
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| claim(&goal));
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(pair[1] <= pair[0] * 3 + 64, "fold affine work: {work:?}");
        }
    }

    #[test]
    fn selected_fold_premises_reuse_one_certificate_scoped_key() {
        let mut work = Vec::new();
        for size in [8usize, 16, 32, 64] {
            let accumulator = Variable(800 + size as u64);
            let item = Variable(900 + size as u64);
            let mut body = machine_fold_body(accumulator.0, item.0);
            for _ in 0..size {
                let shared: crate::kernel::SharedIntegerTerm = body.clone().into();
                body = IntegerTerm::add(shared.as_ref().clone(), body);
            }
            let fold = int32_fold(0, 8, accumulator.0, item.0, body);
            let mut premises = Vec::with_capacity(size);
            let mut nodes = Vec::with_capacity(size);
            for index in 0..size {
                let proposition = proposition(ConditionTerm::IntegerLessEqual(
                    fold.clone().into(),
                    IntegerTerm::constant_i64(index as i64).into(),
                ));
                let result = claim(&proposition);
                premises.push(proposition);
                nodes.push(IntegerArithmeticNode::Premise { index, result });
            }
            let goal = premises[0].clone();
            let certificate = IntegerArithmeticCertificate {
                nodes,
                conclusion: 0,
            };
            reset_fold_alpha_constructions();
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                certificate.check(&goal, &premises).unwrap();
            });
            assert_eq!(
                fold_alpha_constructions(),
                1,
                "fold key rebuilt per certificate"
            );
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3 + 64,
                "certificate fold-key work: {work:?}"
            );
        }
    }

    #[test]
    fn context_free_trivial_integer_claims_check() {
        let x = variable(1);
        let successor = IntegerTerm::Add(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
        );
        let increasing = proposition(ConditionTerm::IntegerGreaterThan(
            crate::kernel::SharedIntegerTerm::from(successor),
            crate::kernel::SharedIntegerTerm::from(x.clone()),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: claim(&increasing),
            }],
            conclusion: 0,
        };
        certificate.check(&increasing, &[]).unwrap();

        let zero = IntegerTerm::Subtract(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(x),
        );
        let identity = proposition(ConditionTerm::IntegerEqual(
            crate::kernel::SharedIntegerTerm::from(zero),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: claim(&identity),
            }],
            conclusion: 0,
        };
        certificate.check(&identity, &[]).unwrap();
    }

    #[test]
    fn scaled_bounds_can_close_an_integer_equality() {
        let x = variable(2);
        let lower = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
            crate::kernel::SharedIntegerTerm::from(x.clone()),
        ));
        let upper = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let goal = proposition(ConditionTerm::IntegerEqual(
            crate::kernel::SharedIntegerTerm::from(x),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let lower_node = premise(0, &lower);
        let upper_node = premise(1, &upper);
        let equality = IntegerAffineClaim {
            relation: IntegerAffineRelation::Equal,
            terms: BTreeMap::from([(IntegerAffineAtom::Variable(Variable(2)), BigInt::one())]),
            constant: BigInt::zero(),
        };
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                lower_node,
                upper_node,
                IntegerArithmeticNode::EqualityFromBounds {
                    lower: 1,
                    upper: 0,
                    result: equality,
                },
            ],
            conclusion: 2,
        };
        certificate.check(&goal, &[lower, upper]).unwrap();
    }

    #[test]
    fn equality_can_supply_one_order_direction_and_be_added() {
        let x = IntegerTerm::Variable(Variable(4));
        let y = IntegerTerm::Variable(Variable(5));
        let equality = proposition(ConditionTerm::IntegerEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(y.clone()),
        ));
        let goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(x),
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
            )),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(y),
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
            )),
        ));
        let equality_node = premise(0, &equality);
        let direction = IntegerAffineClaim {
            relation: IntegerAffineRelation::LessEqual,
            terms: BTreeMap::from([
                (IntegerAffineAtom::Variable(Variable(4)), BigInt::one()),
                (IntegerAffineAtom::Variable(Variable(5)), BigInt::from(-1)),
            ]),
            constant: BigInt::zero(),
        };
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                equality_node,
                IntegerArithmeticNode::EqualityToLessEqual {
                    source: 0,
                    reverse: false,
                    result: direction.clone(),
                },
                IntegerArithmeticNode::Trivial {
                    result: IntegerAffineClaim {
                        relation: IntegerAffineRelation::LessEqual,
                        terms: BTreeMap::new(),
                        constant: BigInt::zero(),
                    },
                },
                IntegerArithmeticNode::Add {
                    left: 1,
                    right: 2,
                    result: direction,
                },
            ],
            conclusion: 3,
        };
        certificate.check(&goal, &[equality]).unwrap();
    }

    #[test]
    fn tampering_with_premise_result_or_inequality_scale_is_rejected() {
        let x = variable(3);
        let premise_proposition = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(5)),
        ));
        let goal = premise_proposition.clone();
        let mut bad_claim = claim(&premise_proposition);
        bad_claim.constant += BigInt::one();
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Premise {
                index: 0,
                result: bad_claim,
            }],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&goal, std::slice::from_ref(&premise_proposition)),
            Err(IntegerArithmeticCheckError::NodeResultMismatch(0))
        );

        let source = premise(0, &premise_proposition);
        let scaled_result = IntegerAffineClaim {
            relation: IntegerAffineRelation::LessEqual,
            terms: BTreeMap::from([(IntegerAffineAtom::Variable(Variable(3)), BigInt::from(2))]),
            constant: BigInt::from(-10),
        };
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                source,
                IntegerArithmeticNode::Scale {
                    source: 0,
                    coefficient: BigInt::from(-2),
                    result: scaled_result,
                },
            ],
            conclusion: 1,
        };
        assert_eq!(
            certificate.check(&goal, &[premise_proposition]),
            Err(IntegerArithmeticCheckError::InvalidCoefficient(1))
        );
    }

    #[test]
    fn deep_integer_terms_are_collected_iteratively() {
        let x = variable(8);
        let mut expression = x.clone();
        for _ in 0..2_048 {
            expression = IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(expression),
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
            );
        }
        let goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(expression),
            crate::kernel::SharedIntegerTerm::from(x),
        ));
        let result = claim(&goal);
        assert!(result.terms.is_empty());
        assert_eq!(result.constant, BigInt::from(2_048));
    }

    #[test]
    fn nonlinear_integer_terms_fail_as_unsupported() {
        let left = variable(10);
        let right = variable(11);
        let goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::Multiply(
                crate::kernel::SharedIntegerTerm::from(left),
                crate::kernel::SharedIntegerTerm::from(right),
            )),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        assert_eq!(
            IntegerArithmeticCertificate {
                nodes: vec![],
                conclusion: 0,
            }
            .check(&goal, &[]),
            Err(IntegerArithmeticCheckError::UnsupportedGoal)
        );
    }

    #[test]
    fn repeated_large_premise_references_use_cached_normalization() {
        let x = variable(9);
        let mut expression = x;
        for _ in 0..256 {
            expression = IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(expression),
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
            );
        }
        let shared_premise = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(expression),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let expected = claim(&shared_premise);
        let shared_nodes = (0..32)
            .map(|_| IntegerArithmeticNode::Premise {
                index: 0,
                result: expected.clone(),
            })
            .collect();
        let shared_certificate = IntegerArithmeticCertificate {
            nodes: shared_nodes,
            conclusion: 31,
        };
        let (_, shared_work) = crate::instrumentation::measure_deterministic_work(|| {
            shared_certificate.check(&shared_premise, std::slice::from_ref(&shared_premise))
        });

        let distinct_premises = (0..32).map(|_| shared_premise.clone()).collect::<Vec<_>>();
        let distinct_nodes = (0..32)
            .map(|index| IntegerArithmeticNode::Premise {
                index,
                result: expected.clone(),
            })
            .collect();
        let distinct_certificate = IntegerArithmeticCertificate {
            nodes: distinct_nodes,
            conclusion: 31,
        };
        let (_, distinct_work) = crate::instrumentation::measure_deterministic_work(|| {
            distinct_certificate.check(&shared_premise, &distinct_premises)
        });

        assert!(shared_work.saturating_mul(4) < distinct_work);
    }

    #[test]
    fn large_integer_scale_accounts_for_product_bit_work() {
        let x = IntegerTerm::Variable(Variable(12));
        let premise_proposition = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let narrow_goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let wide: BigInt = BigInt::one() << 1_024usize;
        let wide_goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::Multiply(
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::Constant(wide.clone())),
                crate::kernel::SharedIntegerTerm::from(x),
            )),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let narrow_claim = claim(&narrow_goal);
        let wide_claim = claim(&wide_goal);
        let narrow_certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &premise_proposition),
                IntegerArithmeticNode::Scale {
                    source: 0,
                    coefficient: BigInt::one(),
                    result: narrow_claim,
                },
            ],
            conclusion: 1,
        };
        let wide_certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &premise_proposition),
                IntegerArithmeticNode::Scale {
                    source: 0,
                    coefficient: wide.clone(),
                    result: wide_claim,
                },
            ],
            conclusion: 1,
        };
        let (_, narrow_work) = crate::instrumentation::measure_deterministic_work(|| {
            narrow_certificate.check(&narrow_goal, std::slice::from_ref(&premise_proposition))
        });
        let (_, wide_work) = crate::instrumentation::measure_deterministic_work(|| {
            wide_certificate.check(&wide_goal, std::slice::from_ref(&premise_proposition))
        });
        assert!(wide_work > narrow_work);
    }
}
