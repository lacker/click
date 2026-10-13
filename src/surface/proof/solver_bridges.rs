//! `auto` on an `Integer` fact whose atoms observe machine values.
//!
//! The solver reads linear `Integer` claims. A proof about `to_integer(i)`
//! usually also needs what the program knows about `i` itself: `i < n` for
//! two `uint64` values says `to_integer(i) < to_integer(n)`, and a `uint64`
//! is never negative. Those facts reach the solver as the steps a proof would
//! write by hand: each connected machine order fact is carried to `Integer`
//! by its bridge theorem (`uint64_less_than_to_integer`, ...), and each
//! unsigned value's observation gets its type range (`uint64_to_integer_bounds`).
//! The solver then runs over the original and the carried facts, and only
//! the carried facts its certificate cites are kept, so the expansion holds
//! the bridges the proof needs and no others. Every step is an `apply` of a
//! standard theorem or an `Integer` certificate; nothing here is trusted.

use super::wide_arithmetic::{Carrier, Relation, apply, have, relate, relation_parts, to_integer};
use super::*;
use crate::surface::checking::{IntegerRefutation, plan_integer_refutation};

/// How many rewrites `auto`'s equality search chains before closing.
const REWRITE_DEPTH: usize = 3;

/// How many connected equalities the search offers, and how many checked
/// rewrites it tries in all. A large connected component fails promptly
/// instead of exploring every short chain of its equalities.
const REWRITE_EQUALITIES: usize = 64;
const REWRITE_ATTEMPTS: usize = 256;

/// How many rewritten goals the search offers to `simp`, after the cheap
/// closers miss: `simp` unfolds and computes what a rewrite exposes.
const REWRITE_SIMP_CLOSURES: usize = 8;

/// How many connected constructor equations `auto` pairs.
const CONSTRUCTOR_EQUATIONS: usize = 16;

/// The machine type an order fact compares, with the names its bridges use.
#[derive(Clone, Copy, Eq, PartialEq)]
enum MachineOrder {
    Int32,
    Wide(Carrier),
    /// A 64-bit equality. The kernel's equality does not say whether its
    /// operands are signed, so its bridges are tried for `uint64` and then
    /// `int64`; the other type's application is refused.
    Equal64,
}

impl MachineOrder {
    fn of(proposition: &Proposition) -> Option<Self> {
        if let Some(carrier) = Carrier::of(proposition) {
            return Some(Self::Wide(carrier));
        }
        match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(..)
                | ConditionTerm::Bitvector32SignedLessEqual(..)
                | ConditionTerm::Bitvector32SignedGreaterThan(..)
                | ConditionTerm::Bitvector32SignedGreaterEqual(..),
                _,
            ) => Some(Self::Int32),
            // An `int32` equality; a `uint32` one is refused by the `int32`
            // bridges and left out.
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(..), true) => {
                Some(Self::Int32)
            }
            Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(..), true) => {
                Some(Self::Equal64)
            }
            _ => None,
        }
    }

    /// The types whose bridges may carry this fact.
    fn carriers(self) -> Vec<Self> {
        match self {
            Self::Equal64 => vec![Self::Wide(Carrier::UInt64), Self::Wide(Carrier::Int64)],
            order => vec![order],
        }
    }

    /// The bridge prefix. `Equal64` reaches a bridge only through
    /// `carriers`.
    fn name(self) -> &'static str {
        match self {
            Self::Int32 => "int32",
            Self::Wide(carrier) => carrier.name(),
            Self::Equal64 => "uint64",
        }
    }

    fn typed_literals(self, expression: &ContractExpression) -> ContractExpression {
        match self {
            Self::Int32 | Self::Equal64 => expression.clone(),
            Self::Wide(carrier) => carrier.typed_literals(expression),
        }
    }

    /// The type range of an unsigned value's observation, when the standard
    /// library states one.
    fn range(self) -> Option<(&'static str, &'static str, &'static str)> {
        match self {
            Self::Int32 => Some(("int32_to_integer_bounds", "-2147483648", "2147483647")),
            Self::Wide(carrier) => match carrier.name() {
                "uint64" => Some(("uint64_to_integer_bounds", "0", "18446744073709551615")),
                "int64" => Some((
                    "int64_to_integer_bounds",
                    "-9223372036854775808",
                    "9223372036854775807",
                )),
                _ => None,
            },
            Self::Equal64 => None,
        }
    }
}

/// One carried fact: how it is established and its source spelling.
struct Carried {
    establish: Establish,
    surface: ClickProposition,
}

enum Establish {
    /// A fixed sequence of steps.
    Steps(Vec<ProofStep>),
    /// The term-by-term observation of `left + right` or `left - right`:
    /// a signed operation once it is defined, which `auto` proves when it is
    /// not already a fact, and an unsigned one once it stays in range.
    Operation {
        operation: ContractExpression,
        left: ContractExpression,
        right: ContractExpression,
        subtract: bool,
    },
}

thread_local! {
    // A bridge may ask for this operation's definedness or no-wrap bound.
    // Proving that prerequisite can find the same operation among connected
    // machine facts. Re-entering its bridge cannot establish new evidence.
    static ACTIVE_OPERATION_BRIDGES: std::cell::RefCell<Vec<ContractExpression>> = const { std::cell::RefCell::new(Vec::new()) };
}

struct OperationBridgeScope;

impl OperationBridgeScope {
    fn enter(operation: &ContractExpression) -> Option<Self> {
        ACTIVE_OPERATION_BRIDGES.with(|active| {
            let mut active = active.borrow_mut();
            if active.contains(operation) {
                return None;
            }
            active.push(operation.clone());
            Some(Self)
        })
    }
}

impl Drop for OperationBridgeScope {
    fn drop(&mut self) {
        ACTIVE_OPERATION_BRIDGES.with(|active| {
            active.borrow_mut().pop();
        });
    }
}

impl Carried {
    fn establish<'a>(&self, proof: &Proof<'a>) -> Result<Option<Proof<'a>>, ClickError> {
        match &self.establish {
            Establish::Steps(steps) => Ok(steps
                .iter()
                .try_fold(proof.clone(), |proof, step| proof.apply_step(step.clone()))
                .ok()),
            Establish::Operation {
                operation,
                left,
                right,
                subtract,
            } => {
                let stem = if *subtract { "subtract" } else { "add" };
                let arguments = vec![left.clone(), right.clone()];
                let defined = ClickProposition::Defined {
                    expression: operation.clone(),
                };
                let observe = |proof: &Proof<'a>, name: String, requirement: &ClickProposition| {
                    proof
                        .apply_step(have(
                            self.surface.clone(),
                            vec![apply(&name, arguments.clone(), vec![requirement.clone()])],
                        ))
                        .ok()
                };
                for width in ["int32", "int64"] {
                    let name = format!("{width}_{stem}_to_integer");
                    if let Some(next) = observe(proof, name.clone(), &defined) {
                        return Ok(Some(next));
                    }
                }
                // An unsigned operation that does not wrap.
                let guard = if *subtract {
                    relate(to_integer(right), to_integer(left), Relation::LessEqual)
                } else {
                    relate(
                        ContractExpression::Add(
                            Box::new(to_integer(left)),
                            Box::new(to_integer(right)),
                        ),
                        ContractExpression::IntegerLiteral("18446744073709551615".into()),
                        Relation::LessEqual,
                    )
                };
                if let Some(next) = observe(proof, format!("uint64_{stem}_to_integer"), &guard) {
                    return Ok(Some(next));
                }
                let Some(_operation_scope) = OperationBridgeScope::enter(operation) else {
                    return Ok(None);
                };
                // Not yet known to be defined: prove it, then observe.
                if let Some(next) = proof.prove_stated_fact(&defined)? {
                    for width in ["int32", "int64"] {
                        let name = format!("{width}_{stem}_to_integer");
                        if let Some(observed) = observe(&next, name, &defined) {
                            return Ok(Some(observed));
                        }
                    }
                }
                let Some(next) = proof.prove_stated_fact(&guard)? else {
                    return Ok(None);
                };
                Ok(observe(&next, format!("uint64_{stem}_to_integer"), &guard))
            }
        }
    }
}

/// The type range of a machine value's observation, for each type whose
/// range theorem could apply. The wrong types' applications fail when the
/// fact is established, and are left out.
fn range_items(value: &ContractExpression) -> Vec<Carried> {
    let mut items = Vec::new();
    for (theorem, minimum, maximum) in [
        ("int32_to_integer_bounds", "-2147483648", "2147483647"),
        (
            "int64_to_integer_bounds",
            "-9223372036854775808",
            "9223372036854775807",
        ),
        ("uint64_to_integer_bounds", "0", "18446744073709551615"),
    ] {
        let bounds = apply(theorem, vec![value.clone()], Vec::new());
        for bound in [
            relate(
                integer_literal(minimum),
                to_integer(value),
                Relation::LessEqual,
            ),
            relate(
                to_integer(value),
                integer_literal(maximum),
                Relation::LessEqual,
            ),
        ] {
            items.push(Carried {
                establish: Establish::Steps(vec![have(bound.clone(), vec![bounds.clone()])]),
                surface: bound,
            });
        }
    }
    items
}

/// What `auto`'s rewrite search may still spend.
struct RewriteBudget {
    attempts: usize,
    simp_closures: usize,
}

/// An equality in both directions, each with its kernel form.
fn oriented_forms(
    kernel: Proposition,
    surface: ClickProposition,
) -> Vec<(Proposition, ClickProposition)> {
    let reverse = crate::kernel::proof::equality_rewrite::reverse_equality(&kernel).zip(
        super::fixed_state_proofs::reverse_surface_equality(&surface),
    );
    std::iter::once((kernel, surface)).chain(reverse).collect()
}

/// `l == r` for an equality spelled `at(S, l) == at(S, r)` or `at(S, l == r)`.
fn unanchored_equality(surface: &ClickProposition) -> Option<ClickProposition> {
    match surface {
        ClickProposition::At { proposition, .. } => Some(proposition.as_ref().clone()),
        ClickProposition::Comparison {
            left:
                ContractExpression::At {
                    selector: left_selector,
                    expression: left,
                },
            operator,
            right:
                ContractExpression::At {
                    selector: right_selector,
                    expression: right,
                },
        } if left_selector == right_selector => Some(ClickProposition::Comparison {
            left: left.as_ref().clone(),
            operator: *operator,
            right: right.as_ref().clone(),
        }),
        _ => None,
    }
}

/// The two sides of an algebraic equality fact.
fn algebraic_sides(
    fact: &Proposition,
) -> Option<(&crate::kernel::AlgebraicTerm, &crate::kernel::AlgebraicTerm)> {
    match fact {
        Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(left, right), true) => {
            Some((left, right))
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => Some((left, right)),
        _ => None,
    }
}

fn is_constructor(term: &crate::kernel::AlgebraicTerm) -> bool {
    matches!(
        term.node,
        crate::kernel::AlgebraicTermNode::Constructor { .. }
    )
}

/// An `Integer` literal, negative ones as a negation of their magnitude.
fn integer_literal(text: &str) -> ContractExpression {
    match text.strip_prefix('-') {
        Some(magnitude) => ContractExpression::Negate(Box::new(
            ContractExpression::IntegerLiteral(magnitude.into()),
        )),
        None => ContractExpression::IntegerLiteral(text.into()),
    }
}

/// The sums and differences observed by `to_integer(...)` in `expression`.
fn observed_operations(expression: &ContractExpression, found: &mut Vec<ContractExpression>) {
    if let ContractExpression::Call { name, arguments } = expression
        && name == "to_integer"
        && let [argument] = arguments.as_slice()
        && matches!(
            argument,
            ContractExpression::Add(..) | ContractExpression::Subtract(..)
        )
        && !found.contains(argument)
    {
        found.push(argument.clone());
    }
    match expression {
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            observed_operations(left, found);
            observed_operations(right, found);
        }
        ContractExpression::Negate(value) => observed_operations(value, found),
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                observed_operations(argument, found);
            }
        }
        _ => {}
    }
}

fn proposition_operations(proposition: &ClickProposition) -> Vec<ContractExpression> {
    let mut found = Vec::new();
    if let ClickProposition::Comparison { left, right, .. } = proposition {
        observed_operations(left, &mut found);
        observed_operations(right, &mut found);
    }
    found
}

impl<'a> Proof<'a> {
    /// Close an `Integer` bound goal with the solver after carrying the
    /// connected machine order facts to `Integer`. Any miss leaves the proof
    /// unchanged.
    pub(in crate::surface::proof) fn try_bridged_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal).is_none() {
            return Ok(None);
        }
        let Some(candidates) =
            crate::surface::planning::proposition_search::solver_connected_premises(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        let mut carried = self.carried_machine_facts(&candidates);
        // Every sum or difference an `Integer` claim observes, from the
        // goal, the carried facts, and the connected `defined(...)` facts,
        // and every one nested inside an observed operation: each gets its
        // term-by-term observation and its type range.
        let mut operations = proposition_operations(surface_goal);
        for item in &carried {
            operations.extend(proposition_operations(&item.surface));
        }
        operations.extend(self.defined_operations(&candidates));
        let mut seen: Vec<ContractExpression> = Vec::new();
        while let Some(operation) = operations.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if seen.contains(&operation) {
                continue;
            }
            seen.push(operation.clone());
            let (left, right, subtract) = match &operation {
                ContractExpression::Add(left, right) => (left, right, false),
                ContractExpression::Subtract(left, right) => (left, right, true),
                _ => continue,
            };
            for operand in [left.as_ref(), right.as_ref()] {
                if matches!(
                    operand,
                    ContractExpression::Add(..) | ContractExpression::Subtract(..)
                ) {
                    operations.push(operand.clone());
                }
            }
            let exact = if subtract {
                ContractExpression::Subtract(
                    Box::new(to_integer(left)),
                    Box::new(to_integer(right)),
                )
            } else {
                ContractExpression::Add(Box::new(to_integer(left)), Box::new(to_integer(right)))
            };
            carried.push(Carried {
                surface: relate(to_integer(&operation), exact, Relation::Equal),
                establish: Establish::Operation {
                    left: left.as_ref().clone(),
                    right: right.as_ref().clone(),
                    subtract,
                    operation: operation.clone(),
                },
            });
            carried.extend(range_items(&operation));
        }
        if carried.is_empty() {
            return Ok(None);
        }

        // Establish every carried fact once to learn its kernel form; the
        // solver then picks among them.
        let mut trial = self.clone();
        let mut established: Vec<(Proposition, &Carried)> = Vec::new();
        for item in &carried {
            check_verification_deadline()?;
            let Some(next) = item.establish(&trial)? else {
                continue;
            };
            let Ok(kernel) = next.lower_cited_surface_proposition(&item.surface, "carried fact")
            else {
                continue;
            };
            trial = next;
            established.push((kernel, item));
        }
        let mut premises = candidates;
        premises.extend(established.iter().map(|(kernel, _)| kernel.clone()));
        check_verification_deadline()?;
        let IntegerRefutation::Proved {
            certificate,
            premises: used,
        } = crate::instrumentation::measure_operation(
            "surface",
            "auto solver",
            "auto solver: bridged integer refutation",
            || plan_integer_refutation(goal, &premises),
        )
        else {
            return Ok(None);
        };
        // Keep only the carried facts the certificate cites, in their order.
        let mut proof = self.clone();
        for (kernel, item) in &established {
            if used.contains(kernel) {
                match item.establish(&proof)? {
                    Some(next) => proof = next,
                    None => return Ok(None),
                }
            }
        }
        // A cited fact with no source spelling leaves the certificate
        // unwritable, so the solver does not close the goal.
        let Some(pairs) = used
            .iter()
            .map(
                |premise| match established.iter().find(|(kernel, _)| kernel == premise) {
                    Some((_, item)) => Some((premise.clone(), item.surface.clone())),
                    None => proof
                        .resolve_simp_premises(std::slice::from_ref(premise), &[])
                        .and_then(|mut spelled| spelled.pop()),
                },
            )
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        let Some(surface) = super::smart_closures::integer_plan_to_surface_certificate(
            &certificate,
            &pairs,
            surface_goal,
        ) else {
            return Ok(None);
        };
        attempt::candidate_outcome(proof.apply_step(ProofStep::ArithmeticCertificate(
            ArithmeticCertificate::integer(surface),
        )))
    }

    /// Close an `Integer` equality goal `l == r` by proving `l <= r` and
    /// `r <= l` with `auto` on each stated fact and joining them with
    /// `equal_from_bounds`. Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_solver_equality_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if !crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal).is_some_and(
            |claim| {
                claim.relation
                    == crate::kernel::proof::integer_arithmetic::IntegerAffineRelation::Equal
            },
        ) {
            return Ok(None);
        }
        let ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = surface_goal
        else {
            return Ok(None);
        };
        let lower = relate(left.clone(), right.clone(), Relation::LessEqual);
        let upper = relate(right.clone(), left.clone(), Relation::LessEqual);
        let mut proof = self.clone();
        for bound in [&lower, &upper] {
            let Ok(scope) = proof.begin_have(bound.clone()) else {
                return Ok(None);
            };
            let Some(closed) = scope.try_auto_fact_closure()? else {
                return Ok(None);
            };
            let Ok(joined) = closed.join() else {
                return Ok(None);
            };
            proof = joined;
        }
        let certificate = IntegerCertificate {
            nodes: vec![
                IntegerCertificateNode::Premise {
                    index: 0,
                    proposition: lower.clone(),
                    result: lower,
                },
                IntegerCertificateNode::Premise {
                    index: 1,
                    proposition: upper.clone(),
                    result: upper,
                },
                IntegerCertificateNode::EqualityFromBounds {
                    lower: 0,
                    upper: 1,
                    result: surface_goal.clone(),
                },
            ],
            conclusion: 2,
        };
        attempt::candidate_outcome(proof.apply_step(ProofStep::ArithmeticCertificate(
            ArithmeticCertificate::integer(certificate),
        )))
    }

    /// `auto` on a proposition goal with no C to run: the solver routes,
    /// then `simp`.
    pub(in crate::surface::proof) fn try_auto_proof_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(closed) = self.try_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_bridged_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_machine_goal_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_solver_equality_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_definedness_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_auto_conjunction_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_simp_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_auto_equality_chain_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_constructor_join_closure()? {
            return Ok(Some(closed));
        }
        self.try_wide_equality_solver_closure()
    }

    /// Rewrite the goal by the equality facts connected to it until
    /// `assumption`, `normalize` or another direct closer finishes it: the
    /// congruence step `simp` takes only once its decider has selected the
    /// premises, here offered every connected equality, algebraic `==` facts
    /// included. Each rewrite is an ordinary checked step.
    pub(in crate::surface::proof) fn try_auto_equality_chain_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        use crate::kernel::proof::equality_rewrite::{equality_rewrite_applies, reverse_equality};
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(mut equalities) =
            crate::surface::planning::proposition_search::solver_connected_equalities(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        // Equalities that rewrite the goal itself come first, so the
        // spelling cap keeps the ones a short chain starts from.
        let applies = |kernel: &Proposition| {
            equality_rewrite_applies(goal, kernel)
                || reverse_equality(kernel)
                    .is_some_and(|reverse| equality_rewrite_applies(goal, &reverse))
        };
        equalities.sort_by_key(|equality| !applies(equality));
        let mut candidates: Vec<Vec<(Proposition, ClickProposition)>> = Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            if candidates.len() >= REWRITE_EQUALITIES {
                break;
            }
            let Some((kernel, surface)) = self
                .resolve_simp_premises(std::slice::from_ref(equality), &[])
                .and_then(|mut spelled| spelled.pop())
            else {
                continue;
            };
            // A fact recorded at a statement's entry is spelled there; its
            // unanchored form denotes the same fact where the proof stands
            // when nothing it names has changed since, which lowering and
            // the checked rewrite decide. Offer the unanchored form first.
            if let Some(unanchored) = unanchored_equality(&surface)
                && let Ok(lowered) =
                    self.lower_surface_proposition(&unanchored, "`auto` rewrite equality")
            {
                candidates.push(oriented_forms(lowered, unanchored));
            }
            candidates.push(oriented_forms(kernel, surface));
        }
        if candidates.is_empty() {
            return Ok(None);
        }
        let mut seen = std::collections::BTreeMap::from([(goal.clone(), REWRITE_DEPTH)]);
        let mut budget = RewriteBudget {
            attempts: REWRITE_ATTEMPTS,
            simp_closures: REWRITE_SIMP_CLOSURES,
        };
        self.rewrite_search(
            &candidates,
            &mut vec![false; candidates.len()],
            REWRITE_DEPTH,
            &mut seen,
            &mut budget,
        )
    }

    /// `auto` on a goal about the fields of a value that two connected facts
    /// equate to constructor applications, `t == Node(c, r)` and
    /// `t == Node(Black, Empty)`: it states `Node(c, r) == Node(Black, Empty)`,
    /// proved by rewriting each application to `t`, and `simp` then reads the
    /// fields' equalities (or the constructors' mismatch) from it. At most
    /// `CONSTRUCTOR_EQUATIONS` connected equations are paired.
    pub(in crate::surface::proof) fn try_constructor_join_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(equalities) =
            crate::surface::planning::proposition_search::solver_connected_equalities(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        // Each equation as the value it names, its constructor application,
        // and the fact oriented `application == value`.
        let mut equations: Vec<(
            crate::kernel::AlgebraicTerm,
            ContractExpression,
            ClickProposition,
        )> = Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            if equations.len() >= CONSTRUCTOR_EQUATIONS {
                break;
            }
            let Some((left, right)) = algebraic_sides(equality) else {
                continue;
            };
            let (left_built, right_built) = (is_constructor(left), is_constructor(right));
            if left_built == right_built {
                continue;
            }
            let Some((_, surface)) = self
                .resolve_simp_premises(std::slice::from_ref(equality), &[])
                .and_then(|mut spelled| spelled.pop())
            else {
                continue;
            };
            let ClickProposition::Comparison {
                left: written_left,
                operator: ComparisonOperator::Equal,
                right: written_right,
            } = surface
            else {
                continue;
            };
            let (value, application, value_written) = if left_built {
                (right, written_left, written_right)
            } else {
                (left, written_right, written_left)
            };
            let oriented = ClickProposition::Comparison {
                left: application.clone(),
                operator: ComparisonOperator::Equal,
                right: value_written,
            };
            equations.push((value.clone(), application, oriented));
        }
        for (index, (value, first, first_fact)) in equations.iter().enumerate() {
            for (other, second, second_fact) in &equations[index + 1..] {
                check_verification_deadline()?;
                if value != other || first == second {
                    continue;
                }
                let joined = ClickProposition::Comparison {
                    left: first.clone(),
                    operator: ComparisonOperator::Equal,
                    right: second.clone(),
                };
                let Ok(next) = self.apply_step(have(
                    joined,
                    vec![
                        ProofStep::Rewrite(first_fact.clone()),
                        ProofStep::Rewrite(second_fact.clone()),
                        ProofStep::Normalize,
                    ],
                )) else {
                    continue;
                };
                if next.is_complete() {
                    return Ok(Some(next));
                }
                if let Some(closed) = next.try_simp_closure()? {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// A bounded depth-first search over rewrite sequences: every applicable
    /// equality in either direction, each used at most once, closing after
    /// every step by `assumption`, `normalize` or the direct logical closer.
    /// An orientation whose left side does not occur in the goal costs no
    /// checked step. A goal already reached with at least as many rewrites
    /// left is not explored again, and the whole search tries at most
    /// `REWRITE_ATTEMPTS` rewrites.
    fn rewrite_search(
        &self,
        candidates: &[Vec<(Proposition, ClickProposition)>],
        used: &mut Vec<bool>,
        depth: usize,
        seen: &mut std::collections::BTreeMap<Proposition, usize>,
        budget: &mut RewriteBudget,
    ) -> Result<Option<Self>, ClickError> {
        let Some(current) = self.goal() else {
            return Ok(None);
        };
        for (index, forms) in candidates.iter().enumerate() {
            if used[index] {
                continue;
            }
            for (kernel, surface) in forms {
                check_verification_deadline()?;
                if !crate::kernel::proof::equality_rewrite::equality_rewrite_applies(
                    current, kernel,
                ) {
                    continue;
                }
                if budget.attempts == 0 {
                    return Ok(None);
                }
                budget.attempts -= 1;
                let Ok(rewritten) = self.apply_step(ProofStep::Rewrite(surface.clone())) else {
                    continue;
                };
                let Some(goal) = rewritten.goal().cloned() else {
                    continue;
                };
                let left = depth - 1;
                match seen.get(&goal) {
                    Some(&reached) if reached >= left => continue,
                    Some(_) => {}
                    None => {
                        if let Some(closed) = rewritten.try_close_after_rewrite(budget)? {
                            return Ok(Some(closed));
                        }
                    }
                }
                seen.insert(goal, left);
                if depth > 1 {
                    used[index] = true;
                    let found =
                        rewritten.rewrite_search(candidates, used, depth - 1, seen, budget)?;
                    used[index] = false;
                    if found.is_some() {
                        return Ok(found);
                    }
                }
            }
        }
        Ok(None)
    }

    fn try_close_after_rewrite(
        &self,
        budget: &mut RewriteBudget,
    ) -> Result<Option<Self>, ClickError> {
        // Inside a `have`, the stated fact is the focused goal; the proof
        // around it is not complete yet.
        let closes = |proof: &Self| proof.focused_discharged() || proof.is_complete();
        if let Ok(closed) = self.apply_step(ProofStep::Assumption)
            && closes(&closed)
        {
            return Ok(Some(closed));
        }
        if let Ok(closed) = self.apply_step(ProofStep::Normalize)
            && closes(&closed)
        {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_direct_logical_closure().ok().flatten() {
            return Ok(Some(closed));
        }
        if budget.simp_closures == 0 {
            return Ok(None);
        }
        budget.simp_closures -= 1;
        Ok(self.try_simp_closure()?.filter(closes))
    }

    /// A conjunction goal: each conjunct by `auto` on the stated fact, then
    /// `assumption`, which closes a conjunction whose sides are facts.
    pub(in crate::surface::proof) fn try_auto_conjunction_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(ClickProposition::And(left, right)) = self.surface_goal() else {
            return Ok(None);
        };
        let Some(proof) = self.prove_stated_fact(left)? else {
            return Ok(None);
        };
        let Some(proof) = proof.prove_stated_fact(right)? else {
            return Ok(None);
        };
        attempt::candidate_outcome(proof.apply_step(ProofStep::Assumption))
    }

    /// Prove `fact` where the proof stands with `auto` on the stated fact,
    /// as `have fact by auto;` does.
    fn prove_stated_fact(&self, fact: &ClickProposition) -> Result<Option<Self>, ClickError> {
        let Ok(scope) = self.begin_have(fact.clone()) else {
            return Ok(None);
        };
        let Some(closed) = scope.try_auto_fact_closure()? else {
            return Ok(None);
        };
        Ok(closed.join().ok())
    }

    /// Close `defined(a + b)` or `defined(a - b)` over `int32` or `int64`:
    /// prove both `Integer` bounds of the exact result with `auto`, then
    /// apply the type's `..._defined_by_integer_bounds` theorem.
    pub(in crate::surface::proof) fn try_definedness_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(ClickProposition::Defined { expression }) = self.surface_goal() else {
            return Ok(None);
        };
        let (left, right, subtract) = match expression {
            ContractExpression::Add(left, right) => (left, right, false),
            ContractExpression::Subtract(left, right) => (left, right, true),
            _ => return Ok(None),
        };
        let exact = if subtract {
            ContractExpression::Subtract(Box::new(to_integer(left)), Box::new(to_integer(right)))
        } else {
            ContractExpression::Add(Box::new(to_integer(left)), Box::new(to_integer(right)))
        };
        let stem = if subtract { "subtract" } else { "add" };
        // An operand that is itself an operation must be defined too; prove
        // that first so the outer theorem's conclusion completes the goal.
        let mut base = self.clone();
        for operand in [left.as_ref(), right.as_ref()] {
            if matches!(
                operand,
                ContractExpression::Add(..) | ContractExpression::Subtract(..)
            ) {
                let defined = ClickProposition::Defined {
                    expression: operand.clone(),
                };
                if let Some(next) = base.prove_stated_fact(&defined)? {
                    base = next;
                }
            }
        }
        for (width, minimum, maximum) in [
            ("int32", "-2147483648", "2147483647"),
            ("int64", "-9223372036854775808", "9223372036854775807"),
        ] {
            let lower = ClickProposition::Comparison {
                left: exact.clone(),
                operator: ComparisonOperator::GreaterEqual,
                right: ContractExpression::IntegerLiteral(minimum.into()),
            };
            let upper = relate(
                exact.clone(),
                ContractExpression::IntegerLiteral(maximum.into()),
                Relation::LessEqual,
            );
            let Some(bounded) = base.prove_stated_fact(&lower)? else {
                continue;
            };
            let Some(bounded) = bounded.prove_stated_fact(&upper)? else {
                continue;
            };
            let Ok(applied) = bounded.apply_step(apply(
                &format!("{width}_{stem}_defined_by_integer_bounds"),
                vec![left.as_ref().clone(), right.as_ref().clone()],
                vec![lower, upper],
            )) else {
                continue;
            };
            if applied.is_complete() || applied.goal() != self.goal() {
                return Ok(Some(applied));
            }
            // The goal may also ask that each operand is defined, which
            // the facts already say.
            if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Close a machine order goal `a < b` or `a <= b` by proving its
    /// `Integer` reading with `auto` on the stated fact and carrying it back
    /// with the type's bridge (`uint64_to_integer_less_than_implies_less_than`,
    /// ...). Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_machine_goal_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_machine_goal_solver_closure_for(false)
    }

    /// `try_machine_goal_solver_closure` for a 64-bit equality goal. Its
    /// `Integer` reading is proved before the type is known, so it costs
    /// more than the other machine goals; `auto` tries it last, after
    /// `simp` and its rewrite search.
    pub(in crate::surface::proof) fn try_wide_equality_solver_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_machine_goal_solver_closure_for(true)
    }

    fn try_machine_goal_solver_closure_for(
        &self,
        wide_equality: bool,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if !matches!(goal, Proposition::ConditionIs(_, true)) {
            return Ok(None);
        }
        let Some(order) = MachineOrder::of(goal) else {
            return Ok(None);
        };
        if (order == MachineOrder::Equal64) != wide_equality {
            return Ok(None);
        }
        let Some((lower, upper, relation, true)) = relation_parts(surface_goal) else {
            return Ok(None);
        };
        let stem = match (order, relation) {
            (_, Relation::Equal) => "to_integer_equal_implies_equal",
            (_, Relation::LessEqual) => "to_integer_less_equal_implies_less_equal",
            // `int32` has no strict converse bridge in the standard library.
            (MachineOrder::Wide(_), Relation::Less) => "to_integer_less_than_implies_less_than",
            _ => return Ok(None),
        };
        // The `Integer` reading proved for the previous type, which the next
        // type reuses when its literals read the same.
        let mut proved: Option<(ClickProposition, Self)> = None;
        for order in order.carriers() {
            let lower = order.typed_literals(&lower);
            let upper = order.typed_literals(&upper);
            let observed = relate(to_integer(&lower), to_integer(&upper), relation);
            let proof = match &proved {
                Some((reading, proof)) if *reading == observed => proof.clone(),
                _ => {
                    let Some(proof) = self.prove_integer_reading(&lower, &upper, &observed)? else {
                        continue;
                    };
                    proved = Some((observed.clone(), proof.clone()));
                    proof
                }
            };
            let Ok(applied) = proof.apply_step(apply(
                &format!("{}_{stem}", order.name()),
                vec![lower, upper],
                vec![observed],
            )) else {
                continue;
            };
            if applied.is_complete() || applied.goal() != self.goal() {
                return Ok(Some(applied));
            }
            if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// `observed`, the `Integer` reading of a machine comparison of `lower`
    /// and `upper`, proved by `auto` as a stated fact.
    fn prove_integer_reading(
        &self,
        lower: &ContractExpression,
        upper: &ContractExpression,
        observed: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        // `to_integer(a + b)` can be stated only where `a + b` is defined.
        let mut base = self.clone();
        for side in [lower, upper] {
            if matches!(
                side,
                ContractExpression::Add(..) | ContractExpression::Subtract(..)
            ) {
                let defined = ClickProposition::Defined {
                    expression: side.clone(),
                };
                if let Some(next) = base.prove_stated_fact(&defined)? {
                    base = next;
                }
            }
        }
        let scope = match base.begin_have(observed.clone()) {
            Ok(scope) => scope,
            Err(_) => return Ok(None),
        };
        let Some(closed) = scope.try_auto_fact_closure()? else {
            return Ok(None);
        };
        Ok(closed.join().ok())
    }

    /// The sums and differences named by connected `defined(...)` facts.
    fn defined_operations(&self, candidates: &[Proposition]) -> Vec<ContractExpression> {
        let mut operations = Vec::new();
        for candidate in candidates {
            if !matches!(
                candidate,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedAddOverflows(..)
                        | ConditionTerm::Bitvector32SignedSubtractOverflows(..)
                        | ConditionTerm::Bitvector64SignedAddOverflows(..)
                        | ConditionTerm::Bitvector64SignedSubtractOverflows(..),
                    false
                )
            ) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some((_, ClickProposition::Defined { expression })) = self
                .resolve_simp_premises(std::slice::from_ref(candidate), &[])
                .and_then(|mut spelled| spelled.pop())
                && matches!(
                    expression,
                    ContractExpression::Add(..) | ContractExpression::Subtract(..)
                )
            {
                operations.push(expression);
            }
        }
        operations
    }

    /// The `Integer` reading of each connected machine order fact, and the
    /// type range of each unsigned value they mention.
    fn carried_machine_facts(&self, candidates: &[Proposition]) -> Vec<Carried> {
        let mut carried = Vec::new();
        let mut ranged: Vec<ContractExpression> = Vec::new();
        for candidate in candidates {
            // A 64-bit equality is not carried: rewriting by it serves an
            // `Integer` claim without reading both types' ranges into every
            // solver call.
            let Some(order) =
                MachineOrder::of(candidate).filter(|order| *order != MachineOrder::Equal64)
            else {
                continue;
            };
            crate::instrumentation::record_deterministic_work(1);
            let Some(spelled) = self.resolve_simp_premises(std::slice::from_ref(candidate), &[])
            else {
                continue;
            };
            let Some((_, surface)) = spelled.into_iter().next() else {
                continue;
            };
            let Some((lower, upper, relation, _)) = relation_parts(&surface) else {
                continue;
            };
            let lower = order.typed_literals(&lower);
            let upper = order.typed_literals(&upper);
            let stated = relate(lower.clone(), upper.clone(), relation);
            let mut steps = Vec::new();
            // A negated or reversed order is first stated the bridge's way
            // round, which is the same fact to the kernel.
            if stated != surface {
                steps.push(have(stated.clone(), vec![ProofStep::Assumption]));
            }
            let observed = relate(to_integer(&lower), to_integer(&upper), relation);
            let carry = match relation {
                Relation::Less => vec![apply(
                    &format!("{}_less_than_to_integer", order.name()),
                    vec![lower.clone(), upper.clone()],
                    vec![stated],
                )],
                Relation::LessEqual => vec![apply(
                    &format!("{}_less_equal_to_integer", order.name()),
                    vec![lower.clone(), upper.clone()],
                    vec![stated],
                )],
                // Equal values have equal observations: rewriting by the
                // fact leaves an identity.
                Relation::Equal => vec![ProofStep::Rewrite(stated), ProofStep::Normalize],
            };
            steps.push(have(observed.clone(), carry));
            carried.push(Carried {
                establish: Establish::Steps(steps),
                surface: observed,
            });
            if let Some((theorem, minimum, maximum)) = order.range() {
                for value in [lower, upper] {
                    if matches!(to_integer(&value), ContractExpression::IntegerLiteral(_))
                        || ranged.contains(&value)
                    {
                        continue;
                    }
                    ranged.push(value.clone());
                    let bounds = apply(theorem, vec![value.clone()], Vec::new());
                    for bound in [
                        relate(
                            integer_literal(minimum),
                            to_integer(&value),
                            Relation::LessEqual,
                        ),
                        relate(
                            to_integer(&value),
                            integer_literal(maximum),
                            Relation::LessEqual,
                        ),
                    ] {
                        carried.push(Carried {
                            establish: Establish::Steps(vec![have(
                                bound.clone(),
                                vec![bounds.clone()],
                            )]),
                            surface: bound,
                        });
                    }
                }
            }
        }
        carried
    }
}
