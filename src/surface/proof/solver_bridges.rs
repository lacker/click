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

/// The machine type an order fact compares, with the names its bridges use.
#[derive(Clone, Copy, Eq, PartialEq)]
enum MachineOrder {
    Int32,
    Wide(Carrier),
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
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Int32 => "int32",
            Self::Wide(carrier) => carrier.name(),
        }
    }

    fn typed_literals(self, expression: &ContractExpression) -> ContractExpression {
        match self {
            Self::Int32 => expression.clone(),
            Self::Wide(carrier) => carrier.typed_literals(expression),
        }
    }

    /// The type range of an unsigned value's observation, when the standard
    /// library states one.
    fn range(self) -> Option<(&'static str, &'static str)> {
        match self {
            Self::Wide(carrier) if carrier.name() == "uint64" => {
                Some(("uint64_to_integer_bounds", "18446744073709551615"))
            }
            _ => None,
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
                // Not yet known to be defined: prove it, then observe.
                if let Some(next) = proof.prove_stated_fact(&defined)? {
                    for width in ["int32", "int64"] {
                        let name = format!("{width}_{stem}_to_integer");
                        if let Some(observed) = observe(&next, name, &defined) {
                            return Ok(Some(observed));
                        }
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
                let Some(next) = proof.prove_stated_fact(&guard)? else {
                    return Ok(None);
                };
                Ok(observe(&next, format!("uint64_{stem}_to_integer"), &guard))
            }
        }
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
        for operation in proposition_operations(surface_goal) {
            let (left, right, subtract) = match &operation {
                ContractExpression::Add(left, right) => (left, right, false),
                ContractExpression::Subtract(left, right) => (left, right, true),
                _ => continue,
            };
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
                    operation,
                },
            });
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
        for _ in 0..super::smart_closures::SOLVER_SPELLING_ROUNDS {
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
            // Keep only the carried facts the certificate cites, in their
            // order.
            let mut proof = self.clone();
            for (kernel, item) in &established {
                if used.contains(kernel) {
                    match item.establish(&proof)? {
                        Some(next) => proof = next,
                        None => return Ok(None),
                    }
                }
            }
            let mut pairs = Vec::with_capacity(used.len());
            let mut unspelled = Vec::new();
            for premise in &used {
                if let Some((_, item)) = established.iter().find(|(kernel, _)| kernel == premise) {
                    pairs.push((premise.clone(), item.surface.clone()));
                    continue;
                }
                match proof
                    .resolve_simp_premises(std::slice::from_ref(premise), &[])
                    .and_then(|mut spelled| spelled.pop())
                {
                    Some(pair) => pairs.push(pair),
                    None => unspelled.push(premise.clone()),
                }
            }
            if !unspelled.is_empty() {
                premises.retain(|premise| !unspelled.contains(premise));
                continue;
            }
            let Some(surface) = super::smart_closures::integer_plan_to_surface_certificate(
                &certificate,
                &pairs,
                surface_goal,
            ) else {
                return Ok(None);
            };
            return attempt::candidate_outcome(proof.apply_step(ProofStep::ArithmeticCertificate(
                ArithmeticCertificate::integer(surface),
            )));
        }
        Ok(None)
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
            let Some(bounded) = self.prove_stated_fact(&lower)? else {
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
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if !matches!(goal, Proposition::ConditionIs(_, true)) {
            return Ok(None);
        }
        let Some(order) = MachineOrder::of(goal) else {
            return Ok(None);
        };
        let Some((lower, upper, relation, true)) = relation_parts(surface_goal) else {
            return Ok(None);
        };
        let stem = match (order, relation) {
            (_, Relation::LessEqual) => "to_integer_less_equal_implies_less_equal",
            // `int32` has no strict converse bridge in the standard library.
            (MachineOrder::Wide(_), Relation::Less) => "to_integer_less_than_implies_less_than",
            _ => return Ok(None),
        };
        let lower = order.typed_literals(&lower);
        let upper = order.typed_literals(&upper);
        let observed = relate(to_integer(&lower), to_integer(&upper), relation);
        let scope = match self.begin_have(observed.clone()) {
            Ok(scope) => scope,
            Err(_) => return Ok(None),
        };
        let Some(closed) = scope.try_auto_fact_closure()? else {
            return Ok(None);
        };
        let Ok(proof) = closed.join() else {
            return Ok(None);
        };
        let Ok(applied) = proof.apply_step(apply(
            &format!("{}_{stem}", order.name()),
            vec![lower, upper],
            vec![observed],
        )) else {
            return Ok(None);
        };
        if applied.is_complete() || applied.goal() != self.goal() {
            return Ok(Some(applied));
        }
        Ok(applied.try_direct_logical_closure().ok().flatten())
    }

    /// The `Integer` reading of each connected machine order fact, and the
    /// type range of each unsigned value they mention.
    fn carried_machine_facts(&self, candidates: &[Proposition]) -> Vec<Carried> {
        let mut carried = Vec::new();
        let mut ranged: Vec<ContractExpression> = Vec::new();
        for candidate in candidates {
            let Some(order) = MachineOrder::of(candidate) else {
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
            let stem = match relation {
                Relation::Less => "less_than_to_integer",
                Relation::LessEqual => "less_equal_to_integer",
                Relation::Equal => continue,
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
            steps.push(have(
                observed.clone(),
                vec![apply(
                    &format!("{}_{stem}", order.name()),
                    vec![lower.clone(), upper.clone()],
                    vec![stated],
                )],
            ));
            carried.push(Carried {
                establish: Establish::Steps(steps),
                surface: observed,
            });
            if let Some((theorem, maximum)) = order.range() {
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
                            ContractExpression::IntegerLiteral("0".into()),
                            to_integer(&value),
                            Relation::LessEqual,
                        ),
                        relate(
                            to_integer(&value),
                            ContractExpression::IntegerLiteral(maximum.into()),
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
