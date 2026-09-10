//! Exact mathematical integer terms.
//!
//! `IntegerTerm` is deliberately separate from `Bitvector32Term`: the latter
//! is also the arena for C machine values and therefore carries machine-width
//! and overflow semantics.  Mathematical integers have no C representation.

use super::*;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::fmt;
use std::str::FromStr;

fn charge_integer_bits(value: &BigInt) {
    // BigInt arithmetic and hashing scale with the magnitude, so account for
    // the encoded bit length rather than charging every numeral as a unit.
    crate::instrumentation::record_deterministic_work(value.bits() as usize + 1);
}

fn charge_binary_bits(left: &BigInt, right: &BigInt) {
    charge_integer_bits(left);
    charge_integer_bits(right);
}

fn charge_multiply_bits(left: &BigInt, right: &BigInt) {
    crate::instrumentation::record_deterministic_work(
        (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1),
    );
}

/// A symbolic, signed, unbounded mathematical integer.
///
/// The constructors below perform only root-local canonicalization.  Terms
/// are built bottom-up throughout the kernel, so looking through a complete
/// child tree here would make a long expression quadratic.  Public enum
/// variants remain useful for deserialization and test construction; callers
/// requiring canonical forms should use the constructors.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum IntegerTerm {
    Constant(BigInt),
    Variable(Variable),
    Negate(Box<IntegerTerm>),
    Add(Box<IntegerTerm>, Box<IntegerTerm>),
    Subtract(Box<IntegerTerm>, Box<IntegerTerm>),
    Multiply(Box<IntegerTerm>, Box<IntegerTerm>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum IntegerComparisonOperator {
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Equal,
    NotEqual,
}

impl IntegerTerm {
    pub fn var(variable: Variable) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self::Variable(variable)
    }

    pub fn constant(value: BigInt) -> Self {
        charge_integer_bits(&value);
        Self::Constant(value)
    }

    pub fn constant_i64(value: i64) -> Self {
        Self::Constant(BigInt::from(value))
    }

    pub fn parse_constant(value: &str) -> Option<Self> {
        BigInt::from_str(value).ok().map(Self::constant)
    }

    pub fn as_const(&self) -> Option<&BigInt> {
        match self {
            Self::Constant(value) => Some(value),
            _ => None,
        }
    }

    pub(crate) fn negate(value: Self) -> Self {
        match value {
            Self::Constant(value) => {
                charge_integer_bits(&value);
                Self::Constant(-value)
            }
            Self::Negate(inner) => *inner,
            value => Self::Negate(Box::new(value)),
        }
    }

    pub(crate) fn add(left: Self, right: Self) -> Self {
        if let (Self::Constant(left), Self::Constant(right)) = (&left, &right) {
            charge_binary_bits(left, right);
            return Self::Constant(left + right);
        }
        if left.as_const().is_some_and(Zero::is_zero) {
            return right;
        }
        if right.as_const().is_some_and(Zero::is_zero) {
            return left;
        }
        Self::Add(Box::new(left), Box::new(right))
    }

    pub(crate) fn subtract(left: Self, right: Self) -> Self {
        if let (Self::Constant(left), Self::Constant(right)) = (&left, &right) {
            charge_binary_bits(left, right);
            return Self::Constant(left - right);
        }
        if right.as_const().is_some_and(Zero::is_zero) {
            return left;
        }
        Self::Subtract(Box::new(left), Box::new(right))
    }

    pub(crate) fn multiply(left: Self, right: Self) -> Self {
        if let (Self::Constant(left), Self::Constant(right)) = (&left, &right) {
            charge_multiply_bits(left, right);
            return Self::Constant(left * right);
        }
        if left.as_const().is_some_and(Zero::is_zero) || right.as_const().is_some_and(Zero::is_zero)
        {
            return Self::Constant(BigInt::zero());
        }
        if left.as_const().is_some_and(One::is_one) {
            return right;
        }
        if right.as_const().is_some_and(One::is_one) {
            return left;
        }
        Self::Multiply(Box::new(left), Box::new(right))
    }
}

impl From<i64> for IntegerTerm {
    fn from(value: i64) -> Self {
        Self::constant_i64(value)
    }
}

impl fmt::Display for IntegerTerm {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(value) => value.fmt(formatter),
            Self::Variable(variable) => write!(formatter, "i{}", variable.0),
            Self::Negate(value) => write!(formatter, "(-{value})"),
            Self::Add(left, right) => write!(formatter, "({left} + {right})"),
            Self::Subtract(left, right) => write!(formatter, "({left} - {right})"),
            Self::Multiply(left, right) => write!(formatter, "({left} * {right})"),
        }
    }
}

impl ConditionTerm {
    pub(crate) fn integer_less_than(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left < right)
            }
            _ => Self::IntegerLessThan(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn integer_less_equal(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left <= right)
            }
            _ => Self::IntegerLessEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn integer_greater_than(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left > right)
            }
            _ => Self::IntegerGreaterThan(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn integer_greater_equal(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left >= right)
            }
            _ => Self::IntegerGreaterEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn integer_equal(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left == right)
            }
            _ => Self::IntegerEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn integer_not_equal(left: IntegerTerm, right: IntegerTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                charge_binary_bits(left, right);
                Self::Constant(left != right)
            }
            _ => Self::IntegerNotEqual(Box::new(left), Box::new(right)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arbitrary_precision_constants_and_exact_operations() {
        let wide = BigInt::one() << 256usize;
        let term = IntegerTerm::add(
            IntegerTerm::constant(wide.clone()),
            IntegerTerm::constant_i64(7),
        );
        assert_eq!(term.as_const(), Some(&(wide + 7)));
        assert_eq!(
            IntegerTerm::negate(IntegerTerm::constant_i64(-3)).as_const(),
            Some(&BigInt::from(3))
        );
        assert_eq!(
            IntegerTerm::multiply(IntegerTerm::constant_i64(-6), IntegerTerm::constant_i64(7))
                .as_const(),
            Some(&BigInt::from(-42))
        );
    }

    #[test]
    fn comparison_constructors_fold_only_root_constants() {
        assert_eq!(
            ConditionTerm::integer_less_than(
                IntegerTerm::constant_i64(2),
                IntegerTerm::constant_i64(3)
            ),
            ConditionTerm::Constant(true)
        );
        let x = IntegerTerm::var(Variable(17));
        assert!(matches!(
            ConditionTerm::integer_equal(x.clone(), x),
            ConditionTerm::IntegerEqual(_, _)
        ));
    }

    #[test]
    fn arithmetic_work_scales_with_numeric_bit_length() {
        let (_, small_work) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::add(IntegerTerm::constant_i64(1), IntegerTerm::constant_i64(2))
        });
        let wide = BigInt::one() << 1024usize;
        let (_, wide_work) = crate::instrumentation::measure_deterministic_work(|| {
            IntegerTerm::add(
                IntegerTerm::constant(wide.clone()),
                IntegerTerm::constant(wide),
            )
        });
        assert!(wide_work > small_work * 100);
    }

    #[test]
    fn exact_integer_numeric_work_has_explicit_size_scaling() {
        let mut additions = Vec::new();
        let mut products = Vec::new();
        for bits in [64usize, 128, 256, 512] {
            let magnitude = BigInt::one() << bits;
            let (sum, add_work) = crate::instrumentation::measure_deterministic_work(|| {
                IntegerTerm::add(
                    IntegerTerm::constant(magnitude.clone()),
                    IntegerTerm::constant(-&magnitude - 7),
                )
            });
            assert_eq!(sum.as_const(), Some(&BigInt::from(-7)));
            let (product, product_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    IntegerTerm::multiply(
                        IntegerTerm::constant(magnitude.clone()),
                        IntegerTerm::constant(-&magnitude),
                    )
                });
            assert_eq!(product.as_const(), Some(&-(BigInt::one() << (2 * bits))));
            additions.push(add_work);
            products.push(product_work);
        }
        for pair in additions.windows(2) {
            assert!(pair[1] > pair[0]);
            assert!(
                pair[1] <= 2 * pair[0] + 8,
                "addition charges linear numeric work"
            );
        }
        for pair in products.windows(2) {
            assert!(
                pair[1] > 3 * pair[0],
                "multiplication must not charge only operand lengths"
            );
            assert!(
                pair[1] <= 4 * pair[0] + 8,
                "the conservative product allowance scales by bit products"
            );
        }
    }
}
