//! A general simplex over exact rationals that refutes a set of linear
//! constraints with Farkas multipliers.
//!
//! Each input constraint is `sum(a_j * x_j) + c <= 0` or `... == 0` over
//! integer coefficients. The solver introduces one slack variable per
//! constraint, `s_i = sum(a_j * x_j)`, bounded above by `-c` (and below by
//! `-c` for an equality), and runs the bounded simplex of Dutertre and de
//! Moura with Bland's rule. When a row cannot be repaired, the row and the
//! bounds of its nonbasic variables give nonnegative multipliers whose
//! combination of the input constraints is `0 + k <= 0` with `k > 0`.
//!
//! This is untrusted search. Its only output that matters is the
//! multipliers, which the caller turns into a kernel-checked certificate.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;
use std::fmt;

/// An exact rational in lowest terms with a positive denominator.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct Rational {
    numerator: BigInt,
    denominator: BigInt,
}

impl Rational {
    pub(crate) fn integer(value: BigInt) -> Self {
        Self {
            numerator: value,
            denominator: BigInt::one(),
        }
    }

    fn new(numerator: BigInt, denominator: BigInt) -> Self {
        debug_assert!(!denominator.is_zero());
        let (numerator, denominator) = if denominator.is_negative() {
            (-numerator, -denominator)
        } else {
            (numerator, denominator)
        };
        let divisor = gcd(&numerator, &denominator);
        if divisor.is_one() || divisor.is_zero() {
            Self {
                numerator,
                denominator,
            }
        } else {
            Self {
                numerator: numerator / &divisor,
                denominator: denominator / divisor,
            }
        }
    }

    pub(crate) fn zero() -> Self {
        Self::integer(BigInt::zero())
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    pub(crate) fn is_positive(&self) -> bool {
        self.numerator.is_positive()
    }

    pub(crate) fn numerator(&self) -> &BigInt {
        &self.numerator
    }

    pub(crate) fn denominator(&self) -> &BigInt {
        &self.denominator
    }

    fn add(&self, other: &Self) -> Self {
        Self::new(
            &self.numerator * &other.denominator + &other.numerator * &self.denominator,
            &self.denominator * &other.denominator,
        )
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    fn mul(&self, other: &Self) -> Self {
        Self::new(
            &self.numerator * &other.numerator,
            &self.denominator * &other.denominator,
        )
    }

    fn div(&self, other: &Self) -> Self {
        Self::new(
            &self.numerator * &other.denominator,
            &self.denominator * &other.numerator,
        )
    }

    fn neg(&self) -> Self {
        Self {
            numerator: -&self.numerator,
            denominator: self.denominator.clone(),
        }
    }

    /// Work units for arithmetic on this value, by bit size.
    fn bits(&self) -> usize {
        (self.numerator.bits() + self.denominator.bits()) as usize + 1
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&self.numerator * &other.denominator).cmp(&(&other.numerator * &self.denominator))
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denominator.is_one() {
            write!(formatter, "{}", self.numerator)
        } else {
            write!(formatter, "{}/{}", self.numerator, self.denominator)
        }
    }
}

fn gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut a = left.abs();
    let mut b = right.abs();
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

fn lcm(left: &BigInt, right: &BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        return BigInt::zero();
    }
    (left / gcd(left, right) * right).abs()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Relation {
    LessEqual,
    Equal,
}

/// One input constraint `sum(terms) + constant REL 0` over atom indices.
#[derive(Clone, Debug)]
pub(crate) struct Constraint {
    pub(crate) terms: BTreeMap<usize, BigInt>,
    pub(crate) constant: BigInt,
    pub(crate) relation: Relation,
}

/// How one input constraint enters a refutation. An inequality is used with
/// a positive multiplier; an equality with a nonzero multiplier of either
/// sign, a negative one meaning its reversed direction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FarkasTerm {
    pub(crate) constraint: usize,
    pub(crate) multiplier: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SimplexOutcome {
    /// The constraints are rationally infeasible. Combining them with these
    /// integer multipliers gives `0 + k <= 0` (or `0 + k == 0`) with
    /// `k != 0`, in the inequality case `k > 0`.
    Infeasible(Vec<FarkasTerm>),
    /// A rational assignment to the atoms satisfying every constraint.
    Feasible(BTreeMap<usize, Rational>),
    /// The work budget ran out.
    Exhausted,
}

#[derive(Clone, Debug)]
struct Bound {
    value: Rational,
    constraint: usize,
}

/// Variables `0..atom_count` are atoms; `atom_count + i` is the slack of
/// constraint `i`.
struct Tableau {
    /// For each basic variable, its row: coefficients over nonbasic variables.
    rows: BTreeMap<usize, BTreeMap<usize, Rational>>,
    values: Vec<Rational>,
    lower: Vec<Option<Bound>>,
    upper: Vec<Option<Bound>>,
}

/// Decide the constraints. `charge` is called with work units and returns
/// false when the caller's budget is exhausted.
pub(crate) fn solve(
    atom_count: usize,
    constraints: &[Constraint],
    mut charge: impl FnMut(usize) -> bool,
) -> SimplexOutcome {
    let variable_count = atom_count + constraints.len();
    let mut tableau = Tableau {
        rows: BTreeMap::new(),
        values: vec![Rational::zero(); variable_count],
        lower: vec![None; variable_count],
        upper: vec![None; variable_count],
    };
    for (index, constraint) in constraints.iter().enumerate() {
        let slack = atom_count + index;
        let row: BTreeMap<usize, Rational> = constraint
            .terms
            .iter()
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .map(|(atom, coefficient)| (*atom, Rational::integer(coefficient.clone())))
            .collect();
        if !charge(row.len() + 1) {
            return SimplexOutcome::Exhausted;
        }
        let bound = Rational::integer(-&constraint.constant);
        if row.is_empty() {
            // A constant constraint: either trivially true or a refutation
            // by itself.
            let violated = match constraint.relation {
                Relation::LessEqual => constraint.constant.is_positive(),
                Relation::Equal => !constraint.constant.is_zero(),
            };
            if violated {
                let multiplier = if constraint.constant.is_negative() {
                    -BigInt::one()
                } else {
                    BigInt::one()
                };
                return SimplexOutcome::Infeasible(vec![FarkasTerm {
                    constraint: index,
                    multiplier,
                }]);
            }
            continue;
        }
        tableau.rows.insert(slack, row);
        tableau.upper[slack] = Some(Bound {
            value: bound.clone(),
            constraint: index,
        });
        if constraint.relation == Relation::Equal {
            tableau.lower[slack] = Some(Bound {
                value: bound,
                constraint: index,
            });
        }
    }
    loop {
        // Bland's rule: the smallest violating basic variable.
        let violation = tableau.rows.keys().copied().find_map(|basic| {
            let value = &tableau.values[basic];
            if let Some(lower) = &tableau.lower[basic]
                && value < &lower.value
            {
                return Some((basic, true));
            }
            if let Some(upper) = &tableau.upper[basic]
                && value > &upper.value
            {
                return Some((basic, false));
            }
            None
        });
        let Some((basic, below)) = violation else {
            let model = (0..atom_count)
                .map(|atom| (atom, tableau.values[atom].clone()))
                .collect();
            return SimplexOutcome::Feasible(model);
        };
        let row = tableau.rows[&basic].clone();
        // The smallest nonbasic variable that can move the basic one toward
        // its violated bound.
        let entering = row.iter().find_map(|(&nonbasic, coefficient)| {
            let increase_helps = coefficient.is_positive() == below;
            let can_move = if increase_helps {
                tableau.upper[nonbasic]
                    .as_ref()
                    .is_none_or(|upper| tableau.values[nonbasic] < upper.value)
            } else {
                tableau.lower[nonbasic]
                    .as_ref()
                    .is_none_or(|lower| tableau.values[nonbasic] > lower.value)
            };
            can_move.then_some(nonbasic)
        });
        let Some(entering) = entering else {
            return SimplexOutcome::Infeasible(explain(&tableau, basic, below, &row, constraints));
        };
        let target = if below {
            tableau.lower[basic].as_ref().unwrap().value.clone()
        } else {
            tableau.upper[basic].as_ref().unwrap().value.clone()
        };
        if !pivot_and_update(&mut tableau, basic, entering, target, &mut charge) {
            return SimplexOutcome::Exhausted;
        }
    }
}

/// Pivot `basic` out and `entering` in, then set the leaving variable to
/// `target` and adjust every basic value.
fn pivot_and_update(
    tableau: &mut Tableau,
    basic: usize,
    entering: usize,
    target: Rational,
    charge: &mut impl FnMut(usize) -> bool,
) -> bool {
    let row = tableau.rows.remove(&basic).expect("basic row");
    let pivot = row[&entering].clone();
    // Value update: moving `entering` by theta moves `basic` by pivot*theta.
    let theta = target.sub(&tableau.values[basic]).div(&pivot);
    tableau.values[basic] = target;
    tableau.values[entering] = tableau.values[entering].add(&theta);
    for (other, other_row) in &tableau.rows {
        if let Some(coefficient) = other_row.get(&entering) {
            if !charge(coefficient.bits() + theta.bits()) {
                return false;
            }
            tableau.values[*other] = tableau.values[*other].add(&coefficient.mul(&theta));
        }
    }
    // Solve the row for `entering`: entering = (basic - sum(others)) / pivot.
    let mut solved: BTreeMap<usize, Rational> = BTreeMap::new();
    solved.insert(basic, Rational::integer(BigInt::one()).div(&pivot));
    for (variable, coefficient) in &row {
        if *variable != entering {
            solved.insert(*variable, coefficient.neg().div(&pivot));
        }
    }
    // Substitute into every other row.
    let others: Vec<usize> = tableau.rows.keys().copied().collect();
    for other in others {
        let other_row = tableau.rows.get_mut(&other).expect("row");
        let Some(factor) = other_row.remove(&entering) else {
            continue;
        };
        for (variable, coefficient) in &solved {
            if !charge(factor.bits() + coefficient.bits()) {
                return false;
            }
            let updated = other_row
                .get(variable)
                .cloned()
                .unwrap_or_else(Rational::zero)
                .add(&factor.mul(coefficient));
            if updated.is_zero() {
                other_row.remove(variable);
            } else {
                other_row.insert(*variable, updated);
            }
        }
    }
    tableau.rows.insert(entering, solved);
    true
}

/// Turn a row that cannot be repaired into integer Farkas multipliers.
///
/// The row states `basic = sum(t_j * v_j)` as an identity over the atoms,
/// and every `v_j` with `t_j != 0` is a slack at the bound that blocks it.
/// For a basic variable below its lower bound, combining
/// `t_j * (s_j - u_j) <= 0` for `t_j > 0`, `-t_j * (l_j - s_j) <= 0` for
/// `t_j < 0`, and `l_b - s_b <= 0` gives `l_b - max(rhs) <= 0` with a
/// positive left side. The case above the upper bound is symmetric.
fn explain(
    tableau: &Tableau,
    basic: usize,
    below: bool,
    row: &BTreeMap<usize, Rational>,
    constraints: &[Constraint],
) -> Vec<FarkasTerm> {
    // Rational multipliers per (constraint, sign): a positive value uses the
    // constraint's upper bound (its own `<= 0` direction), a negative value
    // uses its lower bound (only equalities have one).
    let mut multipliers: BTreeMap<usize, Rational> = BTreeMap::new();
    let mut add = |constraint: usize, value: Rational| {
        let entry = multipliers.entry(constraint).or_insert_with(Rational::zero);
        *entry = entry.add(&value);
    };
    let one = Rational::integer(BigInt::one());
    if below {
        let bound = tableau.lower[basic].as_ref().expect("violated lower bound");
        add(bound.constraint, one.neg());
        for (variable, coefficient) in row {
            if coefficient.is_positive() {
                let bound = tableau.upper[*variable]
                    .as_ref()
                    .expect("blocking upper bound");
                add(bound.constraint, coefficient.clone());
            } else {
                let bound = tableau.lower[*variable]
                    .as_ref()
                    .expect("blocking lower bound");
                add(bound.constraint, coefficient.clone());
            }
        }
    } else {
        let bound = tableau.upper[basic].as_ref().expect("violated upper bound");
        add(bound.constraint, one);
        for (variable, coefficient) in row {
            if coefficient.is_positive() {
                let bound = tableau.lower[*variable]
                    .as_ref()
                    .expect("blocking lower bound");
                add(bound.constraint, coefficient.neg());
            } else {
                let bound = tableau.upper[*variable]
                    .as_ref()
                    .expect("blocking upper bound");
                add(bound.constraint, coefficient.neg());
            }
        }
    }
    // Clear denominators.
    let mut scale = BigInt::one();
    for value in multipliers.values() {
        scale = lcm(&scale, value.denominator());
    }
    multipliers
        .into_iter()
        .filter(|(_, value)| !value.is_zero())
        .map(|(constraint, value)| {
            let multiplier = value.numerator() * (&scale / value.denominator());
            debug_assert!(
                constraints[constraint].relation == Relation::Equal || multiplier.is_positive()
            );
            FarkasTerm {
                constraint,
                multiplier,
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn constraint(terms: &[(usize, i64)], constant: i64, relation: Relation) -> Constraint {
        Constraint {
            terms: terms
                .iter()
                .map(|(atom, coefficient)| (*atom, BigInt::from(*coefficient)))
                .collect(),
            constant: BigInt::from(constant),
            relation,
        }
    }

    /// Combine the constraints with the multipliers and check the result is
    /// a constant contradiction.
    fn assert_refutes(constraints: &[Constraint], terms: &[FarkasTerm]) {
        let mut sum: BTreeMap<usize, BigInt> = BTreeMap::new();
        let mut constant = BigInt::zero();
        let mut all_equal = true;
        for term in terms {
            let constraint = &constraints[term.constraint];
            if constraint.relation == Relation::LessEqual {
                assert!(term.multiplier.is_positive(), "{terms:?}");
                all_equal = false;
            }
            for (atom, coefficient) in &constraint.terms {
                *sum.entry(*atom).or_insert_with(BigInt::zero) += coefficient * &term.multiplier;
            }
            constant += &constraint.constant * &term.multiplier;
        }
        assert!(sum.values().all(Zero::is_zero), "{sum:?}");
        if all_equal {
            assert!(!constant.is_zero());
        } else {
            assert!(constant.is_positive(), "{constant}");
        }
    }

    fn no_budget(_: usize) -> bool {
        true
    }

    #[test]
    fn refutes_a_bound_chain() {
        // x <= y, y <= z, z <= 3, x >= 5.
        let constraints = vec![
            constraint(&[(0, 1), (1, -1)], 0, Relation::LessEqual),
            constraint(&[(1, 1), (2, -1)], 0, Relation::LessEqual),
            constraint(&[(2, 1)], -3, Relation::LessEqual),
            constraint(&[(0, -1)], 5, Relation::LessEqual),
        ];
        let SimplexOutcome::Infeasible(terms) = solve(3, &constraints, no_budget) else {
            panic!("expected a refutation");
        };
        assert_refutes(&constraints, &terms);
    }

    #[test]
    fn finds_a_model_when_feasible() {
        let constraints = vec![
            constraint(&[(0, 1), (1, -1)], 0, Relation::LessEqual),
            constraint(&[(1, 1)], -3, Relation::LessEqual),
            constraint(&[(0, -1)], 1, Relation::LessEqual),
        ];
        let SimplexOutcome::Feasible(model) = solve(2, &constraints, no_budget) else {
            panic!("expected a model");
        };
        for constraint in &constraints {
            let mut value = Rational::integer(constraint.constant.clone());
            for (atom, coefficient) in &constraint.terms {
                value = value.add(&Rational::integer(coefficient.clone()).mul(&model[atom]));
            }
            assert!(!value.is_positive());
        }
    }

    #[test]
    fn uses_equalities_in_both_directions() {
        // a == b + c, b == 2, c == 3, a >= 6.
        let constraints = vec![
            constraint(&[(0, 1), (1, -1), (2, -1)], 0, Relation::Equal),
            constraint(&[(1, 1)], -2, Relation::Equal),
            constraint(&[(2, 1)], -3, Relation::Equal),
            constraint(&[(0, -1)], 6, Relation::LessEqual),
        ];
        let SimplexOutcome::Infeasible(terms) = solve(3, &constraints, no_budget) else {
            panic!("expected a refutation");
        };
        assert_refutes(&constraints, &terms);
    }

    #[test]
    fn rational_coefficients_clear_to_integers() {
        // 3x <= 2y, 2y <= 5, 3x >= 6 is infeasible over the rationals.
        let constraints = vec![
            constraint(&[(0, 3), (1, -2)], 0, Relation::LessEqual),
            constraint(&[(1, 2)], -5, Relation::LessEqual),
            constraint(&[(0, -3)], 6, Relation::LessEqual),
        ];
        let SimplexOutcome::Infeasible(terms) = solve(2, &constraints, no_budget) else {
            panic!("expected a refutation");
        };
        assert_refutes(&constraints, &terms);
    }

    #[test]
    fn a_constant_contradiction_is_its_own_refutation() {
        let constraints = vec![constraint(&[], 1, Relation::LessEqual)];
        assert_eq!(
            solve(0, &constraints, no_budget),
            SimplexOutcome::Infeasible(vec![FarkasTerm {
                constraint: 0,
                multiplier: BigInt::one()
            }])
        );
    }

    #[test]
    fn stops_when_the_budget_runs_out() {
        let constraints = vec![
            constraint(&[(0, 1), (1, -1)], 0, Relation::LessEqual),
            constraint(&[(0, -1)], 5, Relation::LessEqual),
            constraint(&[(1, 1)], -3, Relation::LessEqual),
        ];
        assert_eq!(solve(2, &constraints, |_| false), SimplexOutcome::Exhausted);
    }

    #[test]
    fn random_systems_agree_with_brute_force() {
        // Small systems over x, y in a box: a refutation must combine to a
        // contradiction, and a rational model must satisfy every constraint.
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = |modulus: i64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % (2 * modulus as u64 + 1)) as i64 - modulus
        };
        for _ in 0..400 {
            let mut constraints = Vec::new();
            for _ in 0..4 {
                let relation = if next(3) == 0 {
                    Relation::Equal
                } else {
                    Relation::LessEqual
                };
                constraints.push(constraint(
                    &[(0, next(3)), (1, next(3)), (2, next(3))],
                    next(6),
                    relation,
                ));
            }
            match solve(3, &constraints, no_budget) {
                SimplexOutcome::Infeasible(terms) => assert_refutes(&constraints, &terms),
                SimplexOutcome::Feasible(model) => {
                    for constraint in &constraints {
                        let mut value = Rational::integer(constraint.constant.clone());
                        for (atom, coefficient) in &constraint.terms {
                            value = value
                                .add(&Rational::integer(coefficient.clone()).mul(&model[atom]));
                        }
                        match constraint.relation {
                            Relation::LessEqual => assert!(!value.is_positive()),
                            Relation::Equal => assert!(value.is_zero()),
                        }
                    }
                }
                SimplexOutcome::Exhausted => panic!("unbounded budget"),
            }
        }
    }
}
