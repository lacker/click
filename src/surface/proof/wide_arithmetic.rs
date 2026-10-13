//! `arithmetic() using { ... }` on a linear `uint64` or `int64` order or
//! equality goal.
//!
//! The arithmetic certificates read `int32` and `Integer` claims. A 64-bit
//! goal is proved through its exact Integer observations, by the
//! steps a proof would write by hand: each listed 64-bit order premise is
//! carried to Integer order by its bridge theorem, each sum or difference in
//! the premises and the goal is shown to stay in range (an unsigned one does
//! not wrap, a signed one is defined) and then observed term by term, the Integer claim is proved by the Integer certificate, and the
//! bridge back concludes the goal. Every step is an `apply` of a standard
//! theorem or an Integer `arithmetic`, recorded as such, so the expansion is
//! that explicit script and nothing here is trusted.
use super::*;

/// The largest `uint64`, as the no-wrap guard of
/// `uint64_add_to_integer` writes it.
const UINT64_MAX: &str = "18446744073709551615";
/// The range of `int64`, as the definedness theorems write it.
const INT64_MIN: &str = "-9223372036854775808";
const INT64_MAX: &str = "9223372036854775807";

/// Which 64-bit integers a goal orders.
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum Carrier {
    UInt64,
    Int64,
}

impl Carrier {
    pub(super) fn of(proposition: &Proposition) -> Option<Self> {
        match proposition {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector64UnsignedLessThan(..)
                | ConditionTerm::Bitvector64UnsignedLessEqual(..)
                | ConditionTerm::Bitvector64UnsignedGreaterThan(..)
                | ConditionTerm::Bitvector64UnsignedGreaterEqual(..),
                _,
            ) => Some(Self::UInt64),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector64SignedLessThan(..)
                | ConditionTerm::Bitvector64SignedLessEqual(..)
                | ConditionTerm::Bitvector64SignedGreaterThan(..)
                | ConditionTerm::Bitvector64SignedGreaterEqual(..),
                _,
            ) => Some(Self::Int64),
            _ => None,
        }
    }

    pub(super) fn name(self) -> &'static str {
        match self {
            Self::UInt64 => "uint64",
            Self::Int64 => "int64",
        }
    }

    /// Preserve the comparison's implicit promotion when emitting arguments
    /// for a bridge whose binders explicitly require a 64-bit value.
    pub(super) fn typed_literals(self, expression: &ContractExpression) -> ContractExpression {
        match expression {
            ContractExpression::IntegerLiteral(text) => {
                let value = match self {
                    Self::UInt64 => text
                        .parse::<u64>()
                        .ok()
                        .map(|value| CValue::UInt64(Bitvector32Term::UInt64Constant(value))),
                    Self::Int64 => text
                        .parse::<i64>()
                        .ok()
                        .map(|value| CValue::Int64(Bitvector32Term::Int64Constant(value))),
                };
                value
                    .map(|value| ContractExpression::CFragment(CExpression::Value(value)))
                    .unwrap_or_else(|| expression.clone())
            }
            ContractExpression::Add(left, right) => ContractExpression::Add(
                Box::new(self.typed_literals(left)),
                Box::new(self.typed_literals(right)),
            ),
            ContractExpression::Subtract(left, right) => ContractExpression::Subtract(
                Box::new(self.typed_literals(left)),
                Box::new(self.typed_literals(right)),
            ),
            ContractExpression::At {
                selector,
                expression,
            } => {
                let read = at_operand(selector, expression);
                if matches!(read, ContractExpression::At { .. }) {
                    read
                } else {
                    self.typed_literals(&read)
                }
            }
            _ => expression.clone(),
        }
    }

    /// The bridge theorem `<type>_<stem>`.
    fn theorem(self, stem: &str) -> String {
        format!("{}_{stem}", self.name())
    }
}

/// How a premise or a goal relates its two sides.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Relation {
    Less,
    LessEqual,
    Equal,
}

/// `left < right`, `left <= right` or `left == right`, as the bridges state
/// them. A comparison written the other way round is read with its sides
/// exchanged, and so is a negated order: `not a < b` is `b <= a`, which
/// holds of every pair of values of one integer type. The last part says
/// whether the proposition is written in the bridge's own form.
pub(super) fn relation_parts(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression, Relation, bool)> {
    if let ClickProposition::At {
        selector,
        proposition,
    } = proposition
    {
        let (lower, upper, relation, forward) = relation_parts(proposition)?;
        return Some((
            at_operand(selector, &lower),
            at_operand(selector, &upper),
            relation,
            forward,
        ));
    }
    let (proposition, negated) = match proposition {
        ClickProposition::Not(body) => (body.as_ref(), true),
        other => (other, false),
    };
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let (lower, upper, relation, written_forward) = match (operator, negated) {
        (ComparisonOperator::LessThan, false) => (left, right, Relation::Less, true),
        (ComparisonOperator::LessEqual, false) => (left, right, Relation::LessEqual, true),
        (ComparisonOperator::GreaterThan, false) => (right, left, Relation::Less, false),
        (ComparisonOperator::GreaterEqual, false) => (right, left, Relation::LessEqual, false),
        (ComparisonOperator::Equal, false) => (left, right, Relation::Equal, true),
        (ComparisonOperator::LessThan, true) => (right, left, Relation::LessEqual, false),
        (ComparisonOperator::LessEqual, true) => (right, left, Relation::Less, false),
        (ComparisonOperator::GreaterThan, true) => (left, right, Relation::LessEqual, false),
        (ComparisonOperator::GreaterEqual, true) => (left, right, Relation::Less, false),
        _ => return None,
    };
    Some((lower.clone(), upper.clone(), relation, written_forward))
}

/// Read linear arithmetic in its named snapshot. Constants are independent
/// of memory; each other operand retains the selector checked by lowering.
fn at_operand(selector: &SnapshotSelector, expression: &ContractExpression) -> ContractExpression {
    match expression {
        ContractExpression::IntegerLiteral(_)
        | ContractExpression::CFragment(CExpression::Value(
            CValue::UInt64(Bitvector32Term::UInt64Constant(_))
            | CValue::Int64(Bitvector32Term::Int64Constant(_)),
        ))
        | ContractExpression::At { .. }
        | ContractExpression::Old(_) => expression.clone(),
        ContractExpression::Add(left, right) => ContractExpression::Add(
            Box::new(at_operand(selector, left)),
            Box::new(at_operand(selector, right)),
        ),
        ContractExpression::Subtract(left, right) => ContractExpression::Subtract(
            Box::new(at_operand(selector, left)),
            Box::new(at_operand(selector, right)),
        ),
        _ => ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(expression.clone()),
        },
    }
}

pub(super) fn relate(
    lower: ContractExpression,
    upper: ContractExpression,
    relation: Relation,
) -> ClickProposition {
    ClickProposition::Comparison {
        left: lower,
        operator: match relation {
            Relation::Less => ComparisonOperator::LessThan,
            Relation::LessEqual => ComparisonOperator::LessEqual,
            Relation::Equal => ComparisonOperator::Equal,
        },
        right: upper,
    }
}

fn order(lower: ContractExpression, upper: ContractExpression, strict: bool) -> ClickProposition {
    relate(
        lower,
        upper,
        if strict {
            Relation::Less
        } else {
            Relation::LessEqual
        },
    )
}

/// The exact Integer observation of a `uint64` expression. A literal is
/// written as the Integer it is: the Integer certificate reads a premise as
/// it is spelled, and `to_integer(2u64)` spelled out is an atom to it.
pub(super) fn to_integer(expression: &ContractExpression) -> ContractExpression {
    if let ContractExpression::CFragment(CExpression::Value(CValue::PointerInteger(value))) =
        expression
    {
        return to_integer(&ContractExpression::CFragment(CExpression::Value(
            value.numeric_value(),
        )));
    }
    if let ContractExpression::CFragment(CExpression::Value(CValue::UInt64(value))) = expression
        && let Some(constant) = value.uint64_as_const()
    {
        return ContractExpression::IntegerLiteral(constant.to_string());
    }
    if let ContractExpression::CFragment(CExpression::Value(CValue::Int64(value))) = expression
        && let Some(constant) = value.int64_as_const()
    {
        return ContractExpression::IntegerLiteral(constant.to_string());
    }
    ContractExpression::Call {
        name: "to_integer".to_string(),
        arguments: vec![expression.clone()],
    }
}

/// The sums and differences inside `expression`, innermost first.
fn collect_operations(expression: &ContractExpression, operations: &mut Vec<ContractExpression>) {
    if let ContractExpression::Add(left, right) | ContractExpression::Subtract(left, right) =
        expression
    {
        collect_operations(left, operations);
        collect_operations(right, operations);
        if !operations.contains(expression) {
            operations.push(expression.clone());
        }
    }
}

/// The operands of the sums and differences in `expression` that are not
/// themselves one, and are not literals: the values whose type range the
/// Integer claim may need.
fn collect_atoms(expression: &ContractExpression, atoms: &mut Vec<ContractExpression>) {
    match expression {
        ContractExpression::CFragment(CExpression::Value(CValue::PointerInteger(value))) => {
            collect_atoms(
                &ContractExpression::CFragment(CExpression::Value(value.numeric_value())),
                atoms,
            )
        }
        ContractExpression::Add(left, right) | ContractExpression::Subtract(left, right) => {
            collect_atoms(left, atoms);
            collect_atoms(right, atoms);
        }
        ContractExpression::CFragment(CExpression::Value(
            CValue::UInt64(value) | CValue::Int64(value),
        )) if value.uint64_as_const().is_some() || value.int64_as_const().is_some() => {}
        atom => {
            if !atoms.contains(atom) {
                atoms.push(atom.clone());
            }
        }
    }
}

/// Whether `expression` is a linear side: a sum or difference, or a plain
/// operand. A side that is itself a product, a quotient, a shift or a mask
/// is not a linear claim, and an equality over one is left to the families
/// that read those operations. Such an operation inside a sum is an operand
/// like any other: `(n - n % 4u64) - r` is linear in `n`, `n % 4u64` and `r`.
fn linear(expression: &ContractExpression) -> bool {
    !matches!(
        expression,
        ContractExpression::Multiply(..)
            | ContractExpression::Divide(..)
            | ContractExpression::Remainder(..)
            | ContractExpression::ShiftLeft(..)
            | ContractExpression::ShiftRight(..)
            | ContractExpression::BitwiseAnd(..)
            | ContractExpression::BitwiseOr(..)
            | ContractExpression::BitwiseXor(..)
            | ContractExpression::BitwiseNot(..)
            | ContractExpression::Negate(..)
            | ContractExpression::CUnary { .. }
            | ContractExpression::If { .. }
    )
}

/// The 64-bit type a literal written in `expression` has, if one is.
fn literal_carrier(expression: &ContractExpression) -> Option<Carrier> {
    match expression {
        ContractExpression::CFragment(CExpression::Value(CValue::PointerInteger(value))) => {
            literal_carrier(&ContractExpression::CFragment(CExpression::Value(
                value.numeric_value(),
            )))
        }
        ContractExpression::Add(left, right) | ContractExpression::Subtract(left, right) => {
            literal_carrier(left).or_else(|| literal_carrier(right))
        }
        ContractExpression::CFragment(CExpression::Value(CValue::UInt64(_))) => {
            Some(Carrier::UInt64)
        }
        ContractExpression::CFragment(CExpression::Value(CValue::Int64(_))) => Some(Carrier::Int64),
        _ => None,
    }
}

pub(super) fn have(proposition: ClickProposition, proof: Vec<ProofStep>) -> ProofStep {
    ProofStep::Have {
        proposition,
        proof: Box::new(ProofCertificate::from_validated_steps(proof)),
    }
}

pub(super) fn apply(
    name: &str,
    arguments: Vec<ContractExpression>,
    premises: Vec<ClickProposition>,
) -> ProofStep {
    ProofStep::ApplyTheoremUsing {
        application: TheoremApplication {
            name: name.to_string(),
            arguments,
        },
        premises,
    }
}

impl<'a> Proof<'a> {
    /// Closes a `uint64` or `int64` order goal from the listed premises
    /// through their Integer observations. `Err(None)` is any other goal,
    /// which is left to the certificate families; `Err(Some(reason))` is a
    /// 64-bit order goal this route could not prove, with the step that
    /// stopped it.
    pub(in crate::surface::proof) fn try_wide_arithmetic_using(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Result<Self, Option<String>> {
        // The caller wraps a refusal in the original arithmetic step's
        // diagnostic. Preserve bridge failures with raw summaries: rendering
        // their nested goals/premises here would embed a second diagnostic
        // inside that summary (and violate ClickError's debug invariant).
        let goal = self.goal();
        if let Some(carrier) = goal.and_then(|goal| match goal {
            Proposition::ConditionIs(_, true) => Carrier::of(goal),
            _ => None,
        }) {
            return self.wide_arithmetic_with(carrier, surface_premises);
        }
        // An equality does not say which 64-bit type it compares, since
        // the two share one equality. A listed order premise does, and so
        // does a typed literal; with neither, the unsigned reading is
        // tried and then the signed one.
        if !matches!(
            goal,
            Some(Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(..),
                true
            ))
        ) {
            return Err(None);
        }
        if !self
            .surface_goal()
            .and_then(relation_parts)
            .is_some_and(|(left, right, ..)| linear(&left) && linear(&right))
        {
            return Err(None);
        }
        let written = |proposition: &ClickProposition| {
            relation_parts(proposition)
                .and_then(|(lower, upper, ..)| literal_carrier(&lower).or(literal_carrier(&upper)))
        };
        let stated = surface_premises
            .iter()
            .find_map(|premise| {
                self.lower_cited_surface_proposition(premise, "`arithmetic using` premise")
                    .ok()
                    .as_ref()
                    .and_then(Carrier::of)
            })
            .or_else(|| self.surface_goal().and_then(written))
            .or_else(|| surface_premises.iter().find_map(written));
        if let Some(carrier) = stated {
            return self.wide_arithmetic_with(carrier, surface_premises);
        }
        let unsigned = match self.wide_arithmetic_with(Carrier::UInt64, surface_premises) {
            Ok(proof) => return Ok(proof),
            Err(reason) => reason,
        };
        let signed = match self.wide_arithmetic_with(Carrier::Int64, surface_premises) {
            Ok(proof) => return Ok(proof),
            Err(reason) => reason,
        };
        match (unsigned, signed) {
            (Some(unsigned), Some(signed)) => Err(Some(format!(
                "no listed premise says which 64-bit type the equality compares. Read as uint64: {unsigned}. Read as int64: {signed}"
            ))),
            (reason, other) => Err(reason.or(other)),
        }
    }

    /// [`Self::try_wide_arithmetic_using`] for a goal over `carrier`.
    fn wide_arithmetic_with(
        &self,
        carrier: Carrier,
        surface_premises: &[ClickProposition],
    ) -> Result<Self, Option<String>> {
        let ty = carrier.name();
        let describe = crate::surface::diagnostics::describe_contract_expression;
        let spell = crate::surface::printing::source_click_proposition;
        let article = if carrier == Carrier::Int64 { "an" } else { "a" };
        let (goal_lower, goal_upper, goal_relation, goal_forward) = self
            .surface_goal()
            .and_then(relation_parts)
            .ok_or_else(|| Some(format!("the {ty} goal has no source spelling to read")))?;
        if !goal_forward {
            return Err(Some(format!(
                "{article} {ty} goal is read as `left < right` or `left <= right`; write it that way round"
            )));
        }

        let goal_lower = carrier.typed_literals(&goal_lower);
        let goal_upper = carrier.typed_literals(&goal_upper);
        let mut proof = self.clone();
        // The Integer facts established so far, each an exact premise of
        // the Integer steps that follow.
        let mut facts = Vec::new();
        // What is still to be carried to Integer: a listed order premise,
        // or a sum or difference to observe term by term.
        enum Pending {
            Premise(
                ClickProposition,
                ContractExpression,
                ContractExpression,
                Relation,
            ),
            Operation(ContractExpression),
        }
        let mut pending = Vec::new();
        let mut operations = Vec::new();
        let mut atoms = Vec::new();
        let literal = |text: &str| ContractExpression::IntegerLiteral(text.to_string());
        for premise in surface_premises {
            let kernel = self
                .lower_cited_surface_proposition(premise, "`arithmetic using` premise")
                .map_err(|error| {
                    Some(format!(
                        "the premise `{}` could not be read: {}",
                        spell(premise),
                        error.raw_summary()
                    ))
                })?;
            let equality = matches!(
                kernel,
                Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(..), true)
            );
            // An equality the kernel already holds by identity: a local
            // whose value is the other side, `next == i + 1u64` after
            // `next = i + 1`. It needs no bridge, since both observations
            // are one term, but the sum it names is still to be observed.
            if kernel == Proposition::ConditionIs(ConditionTerm::Constant(true), true)
                && let Some((left, right, Relation::Equal, _)) = relation_parts(premise)
            {
                for side in [
                    &carrier.typed_literals(&left),
                    &carrier.typed_literals(&right),
                ] {
                    collect_operations(side, &mut operations);
                    collect_atoms(side, &mut atoms);
                }
                continue;
            }
            if Carrier::of(&kernel) != Some(carrier) && !equality {
                // An Integer premise is used as it is written.
                facts.push(premise.clone());
                continue;
            }
            let (lower, upper, relation, forward) = relation_parts(premise).ok_or(None)?;
            let lower = carrier.typed_literals(&lower);
            let upper = carrier.typed_literals(&upper);
            // A negated order is read with its sides exchanged, which the
            // bridge accepts as the same fact. An order written with `>` is
            // not, and is asked for the other way round.
            if !forward && !matches!(premise, ClickProposition::Not(_)) {
                return Err(Some(format!(
                    "{article} {ty} premise is read as `left < right` or `left <= right`; write `{}` that way round",
                    spell(premise)
                )));
            }
            collect_operations(&lower, &mut operations);
            collect_operations(&upper, &mut operations);
            collect_atoms(&lower, &mut atoms);
            collect_atoms(&upper, &mut atoms);
            pending.push(Pending::Premise(premise.clone(), lower, upper, relation));
        }
        collect_operations(&goal_lower, &mut operations);
        collect_operations(&goal_upper, &mut operations);
        collect_atoms(&goal_lower, &mut atoms);
        collect_atoms(&goal_upper, &mut atoms);
        // An unsigned value's observation is in the type's range. A sum
        // bounded only by another value, `i + 1` under `i < length`, is
        // shown not to wrap from that, with no bound on `length` listed.
        // One application per value written, and only where a sum or
        // difference could need it, or an equality: `n <= 0` leaves
        // `n == 0` because no `uint64` is below zero.
        if carrier == Carrier::UInt64
            && (!operations.is_empty() || goal_relation == Relation::Equal)
        {
            for atom in &atoms {
                let lower = order(literal("0"), to_integer(atom), false);
                let upper = order(to_integer(atom), literal(UINT64_MAX), false);
                let bounds = apply("uint64_to_integer_bounds", vec![atom.clone()], Vec::new());
                let Ok(next) = proof
                    .apply_step(have(lower.clone(), vec![bounds.clone()]))
                    .and_then(|proof| proof.apply_step(have(upper.clone(), vec![bounds])))
                else {
                    continue;
                };
                proof = next;
                facts.push(lower);
                facts.push(upper);
            }
        }
        pending.extend(operations.into_iter().map(Pending::Operation));

        // Each item is tried against the facts so far, and the passes repeat
        // while one succeeds: a sum is observed once the facts keep it in
        // range, and a premise over a signed sum once that sum is defined.
        // At most one pass per item, so the attempts are quadratic in the
        // listed premises and the operations written in them.
        let mut stuck = None;
        while !pending.is_empty() {
            let mut remaining = Vec::new();
            let mut progressed = false;
            let mut stuck_on_operation = false;
            stuck = None;
            for item in pending {
                let attempt = match &item {
                    Pending::Premise(premise, lower, upper, relation) => {
                        let observed = relate(to_integer(lower), to_integer(upper), *relation);
                        // Equal values have equal observations: rewriting
                        // by the premise leaves an identity.
                        // A negated order is first stated as the order it
                        // is, which is the same fact to the kernel.
                        let stated = relate(lower.clone(), upper.clone(), *relation);
                        let restated = if premise != &stated {
                            proof.apply_step(have(stated.clone(), vec![ProofStep::Assumption]))
                        } else {
                            Ok(proof.clone())
                        };
                        // Equal values have equal observations: rewriting
                        // by the premise leaves an identity.
                        let carried = match relation {
                            Relation::Equal => {
                                vec![ProofStep::Rewrite(premise.clone()), ProofStep::Normalize]
                            }
                            order => vec![apply(
                                &carrier.theorem(if *order == Relation::Less {
                                    "less_than_to_integer"
                                } else {
                                    "less_equal_to_integer"
                                }),
                                vec![lower.clone(), upper.clone()],
                                vec![stated],
                            )],
                        };
                        restated
                            .and_then(|proof| proof.apply_step(have(observed.clone(), carried)))
                            .map(|proof| (proof, observed))
                            .map_err(|error| {
                                format!(
                                    "the premise `{}` could not be carried to Integer order: {}",
                                    spell(premise),
                                    error.raw_summary()
                                )
                            })
                    }
                    Pending::Operation(operation) => {
                        let (left, right, subtract) = match operation {
                            ContractExpression::Add(left, right) => (left, right, false),
                            ContractExpression::Subtract(left, right) => (left, right, true),
                            _ => unreachable!("only sums and differences are collected"),
                        };
                        let exact = if subtract {
                            ContractExpression::Subtract(
                                Box::new(to_integer(left)),
                                Box::new(to_integer(right)),
                            )
                        } else {
                            ContractExpression::Add(
                                Box::new(to_integer(left)),
                                Box::new(to_integer(right)),
                            )
                        };
                        let out_of_range = |guard: &ClickProposition| {
                            format!(
                                "the listed premises do not show that `{}` stays within {ty} (`{}`); {article} {ty} sum or difference that may leave its range is not the sum or difference of its operands",
                                describe(operation),
                                spell(guard)
                            )
                        };
                        let arguments = vec![left.as_ref().clone(), right.as_ref().clone()];
                        let stem = if subtract { "subtract" } else { "add" };
                        let prove = |proof: &Self, proposition: &ClickProposition| {
                            proof
                                .apply_step(have(
                                    proposition.clone(),
                                    vec![ProofStep::ArithmeticUsing(facts.clone())],
                                ))
                                .map_err(|error| {
                                    format!(
                                        "{}: {}",
                                        out_of_range(proposition),
                                        error.raw_summary()
                                    )
                                })
                        };
                        // What the observation bridge requires.
                        let required = match carrier {
                            // An unsigned sum does not exceed the type; an
                            // unsigned difference does not go below zero.
                            Carrier::UInt64 => {
                                let guard = if subtract {
                                    order(to_integer(right), to_integer(left), false)
                                } else {
                                    order(exact.clone(), literal(UINT64_MAX), false)
                                };
                                prove(&proof, &guard).map(|proof| (proof, guard))
                            }
                            // A signed operation is defined when its exact
                            // value is in the type's range, by both bounds.
                            Carrier::Int64 => {
                                let lower = ClickProposition::Comparison {
                                    left: exact.clone(),
                                    operator: ComparisonOperator::GreaterEqual,
                                    right: literal(INT64_MIN),
                                };
                                let upper = order(exact.clone(), literal(INT64_MAX), false);
                                let defined = ClickProposition::Defined {
                                    expression: operation.clone(),
                                };
                                prove(&proof, &lower)
                                    .and_then(|proof| prove(&proof, &upper))
                                    .and_then(|proof| {
                                        let bridge = apply(
                                            &carrier.theorem(&format!(
                                                "{stem}_defined_by_integer_bounds"
                                            )),
                                            arguments.clone(),
                                            vec![lower.clone(), upper.clone()],
                                        );
                                        // The bridge concludes that this
                                        // operation does not overflow. Where
                                        // an operand is itself a sum, being
                                        // defined also says that sum is,
                                        // which is a fact by now, and
                                        // `assumption` joins the two.
                                        proof
                                            .apply_step(have(defined.clone(), vec![bridge.clone()]))
                                            .or_else(|_| {
                                                proof.apply_step(have(
                                                    defined.clone(),
                                                    vec![bridge, ProofStep::Assumption],
                                                ))
                                            })
                                            .map_err(|error| {
                                                format!(
                                                    "{}: {}",
                                                    out_of_range(&upper),
                                                    error.raw_summary()
                                                )
                                            })
                                    })
                                    .map(|proof| (proof, defined))
                            }
                        };
                        required.and_then(|(proof, requirement)| {
                            let equation = ClickProposition::Comparison {
                                left: to_integer(operation),
                                operator: ComparisonOperator::Equal,
                                right: exact.clone(),
                            };
                            proof
                                .apply_step(have(
                                    equation.clone(),
                                    vec![apply(
                                        &carrier.theorem(&format!("{stem}_to_integer")),
                                        arguments.clone(),
                                        vec![requirement],
                                    )],
                                ))
                                .map(|proof| (proof, equation))
                                .map_err(|error| {
                                    format!(
                                        "`{}` could not be observed term by term: {}",
                                        describe(operation),
                                        error.raw_summary()
                                    )
                                })
                        })
                    }
                };
                match attempt {
                    Ok((next, fact)) => {
                        proof = next;
                        facts.push(fact);
                        progressed = true;
                        // An observed unsigned sum or difference is itself
                        // a `uint64`, in the type's range. Stating that
                        // gives the Integer step one fact where it would
                        // otherwise need the ranges of every operand.
                        if carrier == Carrier::UInt64
                            && let Pending::Operation(operation) = &item
                        {
                            let lower = order(literal("0"), to_integer(operation), false);
                            let upper = order(to_integer(operation), literal(UINT64_MAX), false);
                            let bounds = apply(
                                "uint64_to_integer_bounds",
                                vec![operation.clone()],
                                Vec::new(),
                            );
                            if let Ok(next) = proof
                                .apply_step(have(lower.clone(), vec![bounds.clone()]))
                                .and_then(|proof| {
                                    proof.apply_step(have(upper.clone(), vec![bounds]))
                                })
                            {
                                proof = next;
                                facts.push(lower);
                                facts.push(upper);
                            }
                        }
                    }
                    Err(reason) => {
                        // Operations come before the premises that need
                        // them, so the first one left is the one to name.
                        if stuck.is_none()
                            || (matches!(item, Pending::Operation(_)) && !stuck_on_operation)
                        {
                            stuck_on_operation = matches!(item, Pending::Operation(_));
                            stuck = Some(reason);
                        }
                        remaining.push(item);
                    }
                }
            }
            pending = remaining;
            if !progressed {
                break;
            }
        }
        // A sum or premise that could not be carried is left as it is: its
        // observation is then one opaque value to the Integer claim, which
        // may not need to look inside it (`x + 1 < 8` from `x <= 6`, for a
        // compound `x`). If the claim does not follow, the reason reported
        // is the item that could not be carried.
        let uncarried = (!pending.is_empty()).then(|| {
            stuck.unwrap_or_else(|| {
                "the listed premises could not be carried to Integer order".to_string()
            })
        });

        let observed_goal = relate(
            to_integer(&goal_lower),
            to_integer(&goal_upper),
            goal_relation,
        );
        proof = proof
            .apply_step(have(
                observed_goal.clone(),
                vec![ProofStep::ArithmeticUsing(facts)],
            ))
            .map_err(|error| {
                Some(match &uncarried {
                    Some(reason) => format!("{reason}: {}", error.raw_summary()),
                    None => format!(
                        "the goal's Integer reading `{}` does not follow from the listed premises' Integer readings by one Integer `arithmetic` step, which combines a pair of order premises and at most one more taken whole; state an intermediate fact with `have` first: {}",
                        spell(&observed_goal),
                        error.raw_summary()
                    ),
                })
            })?;
        let applied = proof
            .apply_step(apply(
                &carrier.theorem(match goal_relation {
                    Relation::Less => "to_integer_less_than_implies_less_than",
                    Relation::LessEqual => "to_integer_less_equal_implies_less_equal",
                    Relation::Equal => "to_integer_equal_implies_equal",
                }),
                vec![goal_lower, goal_upper],
                vec![observed_goal],
            ))
            .map_err(|error| {
                Some(format!(
                    "the Integer claim could not be carried back: {}",
                    error.raw_summary()
                ))
            })?;
        if applied.is_complete() || applied.goal() != self.goal() {
            return Ok(applied);
        }
        applied
            .try_direct_logical_closure()
            .ok()
            .flatten()
            .ok_or_else(|| Some("the bridged goal did not close".to_string()))
    }
}
