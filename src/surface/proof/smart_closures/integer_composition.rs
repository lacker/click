//! Ordinary proofs of the composition fragment of Integer arithmetic plans.
//! Node results use flat linear forms over the original source operands. A
//! node never embeds another node's source tree, even when the plan is a DAG.
use super::*;
use crate::kernel::{IntegerTerm, SharedIntegerTerm};

#[derive(Clone, Default)]
struct Form {
    terms: BTreeMap<u64, BigInt>,
    constant: BigInt,
}

impl Form {
    fn scaled(&self, factor: &BigInt) -> Self {
        Self {
            terms: self
                .terms
                .iter()
                .filter_map(|(key, value)| {
                    let value = value * factor;
                    (!value.is_zero()).then_some((*key, value))
                })
                .collect(),
            constant: &self.constant * factor,
        }
    }
    fn add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.constant += &other.constant;
        for (key, value) in &other.terms {
            *result.terms.entry(*key).or_default() += value;
        }
        result.terms.retain(|_, value| !value.is_zero());
        result
    }
}

struct Atom {
    // Retain the interned term for as long as its id keys a source operand.
    _term: SharedIntegerTerm,
    surface: SyntaxTerm,
}

struct Node {
    form: Form,
    equal: bool,
    claim: SyntaxProposition,
    semantic: IntegerAffineClaim,
}

fn literal(value: &BigInt) -> SyntaxTerm {
    // A fixed-width literal already carries its parsed bits. Observing it
    // keeps repeated large endpoints exact without repeatedly parsing an
    // arbitrary-precision decimal in every theorem argument.
    if value.is_positive()
        && value.bits() > 31
        && let Some(magnitude) = num_traits::ToPrimitive::to_u64(&value.abs())
    {
        let observed = SyntaxTerm::Call {
            name: "to_integer".into(),
            arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                crate::kernel::uint64(OldMachineTerm::uint64_constant(magnitude)),
            ))],
        };
        return observed;
    }
    surface_signed_integer_literal(value)
}
fn zero() -> SyntaxTerm {
    literal(&BigInt::zero())
}
fn add(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Add(Box::new(a), Box::new(b))
}
fn multiply(a: SyntaxTerm, b: SyntaxTerm) -> SyntaxTerm {
    SyntaxTerm::Multiply(Box::new(a), Box::new(b))
}
fn compare(a: SyntaxTerm, equal: bool, b: SyntaxTerm) -> SyntaxProposition {
    // A detached reflexivity or substitution identity has no surrounding
    // Integer operand. Keep constant arithmetic exact in that position too.
    let mut pending = vec![&a, &b];
    let mut closed = true;
    while let Some(term) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match term {
            SyntaxTerm::IntegerLiteral(_) => {}
            SyntaxTerm::Negate(value) => pending.push(value),
            SyntaxTerm::Add(left, right)
            | SyntaxTerm::Subtract(left, right)
            | SyntaxTerm::Multiply(left, right) => pending.extend([left.as_ref(), right.as_ref()]),
            _ => {
                closed = false;
                break;
            }
        }
    }
    let a = if closed {
        super::super::surface_synthesis::integer_typed_expression(a)
    } else {
        a
    };
    SyntaxProposition::Comparison {
        left: a,
        operator: if equal {
            ComparisonOperator::Equal
        } else {
            ComparisonOperator::LessEqual
        },
        right: b,
    }
}
fn application(
    name: &str,
    arguments: Vec<SyntaxTerm>,
    premises: Vec<SyntaxProposition>,
) -> ProofStep {
    ProofStep::ApplyPlannedTheorem {
        application: TheoremApplication {
            name: format!("click::integer::{name}"),
            arguments,
        },
        premises,
    }
}
fn have(claim: SyntaxProposition, steps: Vec<ProofStep>) -> ProofStep {
    super::super::wide_arithmetic::have(claim, steps)
}
fn computational_fact(claim: SyntaxProposition) -> ProofStep {
    // An empty generated body asks run_scope to build a goal-local proof.
    have(claim, Vec::new())
}

fn expression(form: &Form, atoms: &BTreeMap<u64, Atom>) -> SyntaxTerm {
    if form.terms.is_empty() {
        // The callee supplies Integer context for a theorem argument;
        // compare() adds a lexical type only to detached constant claims.
        return literal(&form.constant);
    }

    let mut result = None;
    for (key, coefficient) in &form.terms {
        let term = atoms[key].surface.clone();
        let term = if coefficient.is_one() {
            term
        } else if coefficient == &BigInt::from(-1) {
            SyntaxTerm::Negate(Box::new(term))
        } else {
            multiply(literal(coefficient), term)
        };
        result = Some(match result {
            None => term,
            Some(previous) => add(previous, term),
        });
    }
    if !form.constant.is_zero() || result.is_none() {
        let constant = literal(&form.constant);
        result = Some(match result {
            None => constant,
            Some(previous) => add(previous, constant),
        });
    }
    result.expect("a linear form includes its zero")
}

fn operand(term: &SharedIntegerTerm, surface: SyntaxTerm, atoms: &mut BTreeMap<u64, Atom>) -> Form {
    if let Some(constant) = term.as_const() {
        return Form {
            constant: constant.clone(),
            ..Form::default()
        };
    }
    atoms.entry(term.id()).or_insert_with(|| Atom {
        _term: term.clone(),
        surface,
    });
    Form {
        terms: BTreeMap::from([(term.id(), BigInt::one())]),
        constant: BigInt::zero(),
    }
}

pub(super) fn parts(
    proposition: &Proposition,
) -> Option<(&SharedIntegerTerm, bool, &SharedIntegerTerm)> {
    match proposition {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((OldConditionTerm::IntegerLessEqual(a, b), _)) =
                condition_source_0.old_condition() =>
        {
            Some((a, false, b))
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((OldConditionTerm::IntegerGreaterEqual(a, b), _)) =
                condition_source_0.old_condition() =>
        {
            Some((b, false, a))
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((OldConditionTerm::IntegerEqual(a, b), _)) =
                condition_source_0.old_condition() =>
        {
            Some((a, true, b))
        }
        _ => None,
    }
}

#[derive(Clone)]
struct Reading {
    left: SharedIntegerTerm,
    right: SharedIntegerTerm,
    equal: bool,
    strict: bool,
}

fn reading(proposition: &Proposition) -> Option<Reading> {
    let mut proposition = proposition;
    let mut negative = false;
    while let Proposition::Not(body) = proposition {
        negative = !negative;
        proposition = body;
    }
    let Proposition::ConditionIs(condition, truth) = proposition else {
        return None;
    };
    let truth = *truth != negative;
    if matches!(condition.old_form(), OldConditionTerm::Compare { .. }) {
        let observed =
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                &Proposition::condition_is(condition.clone(), truth),
            )
            .into_iter()
            .next()?;
        return reading(&observed);
    }
    let (a, b, equal, strict, reverse) = match (condition.old_form(), truth) {
        (OldConditionTerm::IntegerEqual(a, b), true)
        | (OldConditionTerm::IntegerNotEqual(a, b), false) => (a, b, true, false, false),
        (OldConditionTerm::IntegerLessEqual(a, b), true)
        | (OldConditionTerm::IntegerGreaterThan(a, b), false) => (a, b, false, false, false),
        (OldConditionTerm::IntegerGreaterEqual(a, b), true)
        | (OldConditionTerm::IntegerLessThan(a, b), false) => (a, b, false, false, true),
        (OldConditionTerm::IntegerLessThan(a, b), true)
        | (OldConditionTerm::IntegerGreaterEqual(a, b), false) => (a, b, false, true, false),
        (OldConditionTerm::IntegerGreaterThan(a, b), true)
        | (OldConditionTerm::IntegerLessEqual(a, b), false) => (a, b, false, true, true),
        _ => return None,
    };
    Some(Reading {
        left: if reverse { b.clone() } else { a.clone() },
        right: if reverse { a.clone() } else { b.clone() },
        equal,
        strict,
    })
}

/// Native equalities and promoted comparisons can have more than one exact
/// Integer reading. Use the carrier selected by the plan's named result.
fn reading_matching(proposition: &Proposition, claim: &IntegerAffineClaim) -> Option<Reading> {
    let mut source = proposition;
    let mut negative = false;
    while let Proposition::Not(inner) = source {
        negative = !negative;
        source = inner;
    }
    let native = match source {
        Proposition::ConditionIs(condition, truth) => {
            Proposition::condition_is(condition.clone(), *truth != negative)
        }
        other => other.clone(),
    };
    let readings =
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(&native);
    if readings.is_empty() {
        return (integer_affine_claim(proposition).as_ref() == Some(claim))
            .then(|| reading(proposition))
            .flatten();
    }
    readings.iter().find_map(|proposition| {
        (integer_affine_claim(proposition).as_ref() == Some(claim))
            .then(|| reading(proposition))
            .flatten()
    })
}

pub(super) fn canonical_surface(surface: &SyntaxProposition) -> Option<SyntaxProposition> {
    let anchored = surface_comparison_with_anchored_operands(surface);
    let mut surface = &anchored;
    let mut negative = false;
    while let SyntaxProposition::Not(body) = surface {
        negative = !negative;
        surface = body;
    }
    let SyntaxProposition::Comparison {
        left,
        operator,
        right,
    } = surface
    else {
        return None;
    };
    let operator = if negative {
        match operator {
            ComparisonOperator::Equal => ComparisonOperator::NotEqual,
            ComparisonOperator::NotEqual => ComparisonOperator::Equal,
            ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
            ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
            ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
            ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
            _ => return None,
        }
    } else {
        *operator
    };
    let (left, operator, right) = match operator {
        ComparisonOperator::GreaterEqual => {
            (right.clone(), ComparisonOperator::LessEqual, left.clone())
        }
        ComparisonOperator::GreaterThan => {
            (right.clone(), ComparisonOperator::LessThan, left.clone())
        }
        operator => (left.clone(), operator, right.clone()),
    };
    Some(SyntaxProposition::Comparison {
        left,
        operator,
        right,
    })
}

fn prepare_relation(
    relation: Reading,
    canonical: &SyntaxProposition,
    source: &SyntaxProposition,
    atoms: &mut BTreeMap<u64, Atom>,
) -> (Form, bool, Vec<ProofStep>) {
    let (left, operator, right) = integer_surface_ordered_parts(canonical).expect("ordered source");
    // A native constant expression must remain its evaluated value when it
    // becomes an Integer theorem argument. Re-state that value explicitly;
    // contextual Integer arithmetic can otherwise retain a different tree.
    let mut left = relation.left.as_const().map(literal).unwrap_or(left);
    let right = relation.right.as_const().map(literal).unwrap_or(right);
    let mut form = operand(&relation.left, left.clone(), atoms)
        .add(&operand(&relation.right, right.clone(), atoms).scaled(&BigInt::from(-1)));
    let mut body = Vec::new();
    let mut ordered = SyntaxProposition::Comparison {
        left: left.clone(),
        operator,
        right: right.clone(),
    };
    if &ordered != source {
        body.push(have(ordered.clone(), vec![ProofStep::Known]));
    }
    if relation.strict {
        form.constant += 1;
        let shifted = compare(
            add(left.clone(), literal(&BigInt::one())),
            false,
            right.clone(),
        );
        body.push(have(
            shifted.clone(),
            vec![application(
                "lt_step_le",
                vec![left.clone(), right.clone()],
                vec![ordered],
            )],
        ));
        left = add(left, literal(&BigInt::one()));
        ordered = shifted;
    }
    let target = compare(expression(&form, atoms), relation.equal, zero());
    if !relation.equal {
        let value = expression(&form, atoms);
        let identity = compare(
            value.clone(),
            true,
            SyntaxTerm::Subtract(Box::new(left.clone()), Box::new(right.clone())),
        );
        body.push(computational_fact(identity.clone()));
        body.push(application(
            "le_difference",
            vec![left, right, value],
            vec![ordered, identity],
        ));
        return (form, false, body);
    }

    let shifted = compare(
        SyntaxTerm::Subtract(Box::new(left.clone()), Box::new(right.clone())),
        true,
        zero(),
    );
    body.push(have(
        shifted.clone(),
        vec![application(
            "equal_difference",
            vec![left, right],
            vec![ordered],
        )],
    ));
    body.extend(transfer(&target, &shifted));
    (form, relation.equal, body)
}

fn restore(target: &SyntaxProposition, node: &Node, atoms: &BTreeMap<u64, Atom>) -> Vec<ProofStep> {
    let (_, operator, right) = integer_surface_non_strict_parts(target).expect("ordered target");
    let equal = operator == ComparisonOperator::Equal;
    if !equal {
        let (left, _, right) = integer_surface_non_strict_parts(target).expect("ordered target");
        let value = expression(&node.form, atoms);
        let identity = compare(
            value.clone(),
            true,
            SyntaxTerm::Subtract(Box::new(left.clone()), Box::new(right.clone())),
        );
        return vec![
            computational_fact(identity.clone()),
            application(
                "difference_le",
                vec![left, right, value],
                vec![node.claim.clone(), identity],
            ),
        ];
    }
    let value = expression(&node.form, atoms);
    let reflexive = compare(right.clone(), equal, right.clone());
    let fact = compare(
        add(value.clone(), right.clone()),
        equal,
        add(zero(), right.clone()),
    );
    let mut body = vec![have(
        fact.clone(),
        vec![application(
            if equal { "equal_add" } else { "add_le" },
            vec![value, zero(), right.clone(), right],
            vec![node.claim.clone(), reflexive],
        )],
    )];
    let (left, _, right) = integer_surface_non_strict_parts(target).expect("ordered target");
    let non_strict = compare(left, equal, right);
    body.extend(transfer(&non_strict, &fact));
    body
}

fn disequality_operands(proposition: &Proposition) -> Vec<(SharedIntegerTerm, SharedIntegerTerm)> {
    let mut p = proposition;
    let mut negative = false;
    while let Proposition::Not(body) = p {
        negative = !negative;
        p = body;
    }
    let Proposition::ConditionIs(c, v) = p else {
        return Vec::new();
    };
    if matches!(c.old_form(), OldConditionTerm::Compare { .. }) {
        return crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::condition_is(c.clone(), *v != negative),
        )
        .iter()
        .flat_map(disequality_operands)
        .collect();
    }
    match (c.old_form(), *v != negative) {
        (OldConditionTerm::IntegerNotEqual(a, b), true)
        | (OldConditionTerm::IntegerEqual(a, b), false) => vec![(a.clone(), b.clone())],
        _ => Vec::new(),
    }
}

fn strict_node(
    proof: &Proof<'_>,
    bound: &Node,
    disequal: &(Proposition, SyntaxProposition),
    atoms: &mut BTreeMap<u64, Atom>,
) -> Result<(Form, bool, Vec<ProofStep>), ClickError> {
    let observed = observed_native_surface_comparison(&disequal.0, &disequal.1);
    let lowered = proof.lower_cited_surface_proposition(&observed, "Integer disequality")?;
    let (a, b, reverse) = disequality_operands(&lowered)
        .into_iter()
        .find_map(|(a, b)| {
            for reverse in [false, true] {
                let (left, right) = if reverse { (&b, &a) } else { (&a, &b) };
                let forward = Proposition::condition_is(
                    OldConditionTerm::IntegerLessEqual(left.clone(), right.clone()),
                    true,
                );
                if integer_affine_claim(&forward).as_ref() == Some(&bound.semantic) {
                    return Some(if reverse { (b, a, true) } else { (a, b, false) });
                }
            }
            None
        })
        .ok_or_else(|| proof.step_error("Integer strictness requires its bound's disequality"))?;
    let canonical = canonical_surface(&observed)
        .ok_or_else(|| proof.step_error("Integer disequality has no comparison spelling"))?;
    let SyntaxProposition::Comparison {
        left,
        operator: ComparisonOperator::NotEqual,
        right,
    } = canonical
    else {
        return Err(proof.step_error("Integer strictness requires a disequality spelling"));
    };
    let (mut left, mut right) = (left, right);
    if reverse {
        std::mem::swap(&mut left, &mut right);
    }
    let ordered = compare(left.clone(), false, right.clone());
    let neq = SyntaxProposition::Comparison {
        left: left.clone(),
        operator: ComparisonOperator::NotEqual,
        right: right.clone(),
    };
    let strict = SyntaxProposition::Comparison {
        left: left.clone(),
        operator: ComparisonOperator::LessThan,
        right: right.clone(),
    };
    let mut body = vec![
        have(ordered.clone(), restore(&ordered, bound, atoms)),
        have(neq.clone(), vec![ProofStep::Known]),
        have(
            strict.clone(),
            vec![application(
                "le_ne_lt",
                vec![left, right],
                vec![ordered, neq],
            )],
        ),
    ];
    let (form, equal, tail) = prepare_relation(
        Reading {
            left: a,
            right: b,
            equal: false,
            strict: true,
        },
        &strict,
        &strict,
        atoms,
    );
    body.extend(tail);
    Ok((form, equal, body))
}

// When a linear refutation uses the negated goal once, cancel that
// assumption in the plan itself. The remaining selected facts prove the
// goal directly; there is no reason to construct a double-negation proof.
fn direct_refutation(
    plan: &IntegerArithmeticPlan,
    goal: &IntegerAffineClaim,
) -> Option<IntegerArithmeticPlan> {
    if goal.relation != IntegerAffineRelation::LessEqual
        || !contradiction_claim(node_claim(plan.nodes.get(plan.conclusion)?))
    {
        return None;
    }
    let mut weights: Vec<BigInt> = Vec::with_capacity(plan.nodes.len());
    let mut negated = None;
    for node in &plan.nodes {
        crate::instrumentation::record_deterministic_work(1);
        let weight = match node {
            IntegerArithmeticNode::NegatedGoal { result } => {
                if negated.replace(result.clone()).is_some() {
                    return None;
                }
                BigInt::one()
            }
            IntegerArithmeticNode::Scale {
                source,
                coefficient,
                ..
            } => {
                let weight = weights.get(*source)?;
                if crate::instrumentation::deadline_exceeded_with_work(
                    (weight.bits() as usize + 1).saturating_mul(coefficient.bits() as usize + 1),
                ) {
                    return None;
                }
                weight * coefficient
            }
            IntegerArithmeticNode::Add { left, right, .. } => {
                weights.get(*left)? + weights.get(*right)?
            }
            IntegerArithmeticNode::EqualityToLessEqual {
                source, reverse, ..
            } => {
                let weight = weights.get(*source)?.clone();
                if *reverse { -weight } else { weight }
            }
            IntegerArithmeticNode::Premise { .. }
            | IntegerArithmeticNode::TypeRange { .. }
            | IntegerArithmeticNode::OperationBound { .. }
            | IntegerArithmeticNode::ExcludedTypeBound { .. }
            | IntegerArithmeticNode::Trivial { .. } => BigInt::zero(),
            _ => return None,
        };
        weights.push(weight);
    }
    if !weights.get(plan.conclusion)?.is_one() {
        return None;
    }
    let negated = negated?;
    let mut mapping = Vec::with_capacity(plan.nodes.len());
    let mut nodes = Vec::with_capacity(plan.nodes.len());
    for (index, node) in plan.nodes.iter().enumerate() {
        let mut result = node_claim(node).clone();
        for (atom, coefficient) in &negated.terms {
            if crate::instrumentation::deadline_exceeded_with_work(
                (coefficient.bits() as usize + 1)
                    .saturating_mul(weights[index].bits() as usize + 1),
            ) {
                return None;
            }
            *result.terms.entry(atom.clone()).or_default() -= coefficient * &weights[index];
        }
        result.terms.retain(|_, coefficient| !coefficient.is_zero());
        result.constant -= &negated.constant * &weights[index];
        let new_node = match node {
            IntegerArithmeticNode::NegatedGoal { .. } => {
                mapping.push(None);
                continue;
            }
            IntegerArithmeticNode::Scale {
                source,
                coefficient,
                ..
            } => {
                let Some(source) = mapping[*source] else {
                    mapping.push(None);
                    continue;
                };
                IntegerArithmeticNode::Scale {
                    source,
                    coefficient: coefficient.clone(),
                    result,
                }
            }
            IntegerArithmeticNode::Add { left, right, .. } => {
                match (mapping[*left], mapping[*right]) {
                    (Some(left), Some(right)) => IntegerArithmeticNode::Add {
                        left,
                        right,
                        result,
                    },
                    (left, right) => {
                        mapping.push(left.or(right));
                        continue;
                    }
                }
            }
            IntegerArithmeticNode::EqualityToLessEqual {
                source, reverse, ..
            } => {
                let Some(source) = mapping[*source] else {
                    mapping.push(None);
                    continue;
                };
                IntegerArithmeticNode::EqualityToLessEqual {
                    source,
                    reverse: *reverse,
                    result,
                }
            }
            other => other.clone(),
        };
        mapping.push(Some(nodes.len()));
        nodes.push(new_node);
    }
    let mut conclusion = mapping[plan.conclusion]?;
    let actual = node_claim(&nodes[conclusion]);
    if actual.terms != goal.terms || actual.relation != goal.relation {
        return None;
    }
    let slack = &actual.constant - &goal.constant;
    if slack.is_negative() {
        return None;
    }
    if !slack.is_zero() {
        let trivial = nodes.len();
        nodes.push(IntegerArithmeticNode::Trivial {
            result: IntegerAffineClaim {
                relation: IntegerAffineRelation::LessEqual,
                terms: BTreeMap::new(),
                constant: -slack,
            },
        });
        nodes.push(IntegerArithmeticNode::Add {
            left: conclusion,
            right: trivial,
            result: goal.clone(),
        });
        conclusion = nodes.len() - 1;
    }
    Some(IntegerArithmeticPlan { nodes, conclusion })
}

fn node_claim(node: &IntegerArithmeticNode) -> &IntegerAffineClaim {
    match node {
        IntegerArithmeticNode::Premise { result, .. }
        | IntegerArithmeticNode::Scale { result, .. }
        | IntegerArithmeticNode::Add { result, .. }
        | IntegerArithmeticNode::EqualityToLessEqual { result, .. }
        | IntegerArithmeticNode::EqualityFromBounds { result, .. }
        | IntegerArithmeticNode::Trivial { result }
        | IntegerArithmeticNode::NegatedGoal { result }
        | IntegerArithmeticNode::TypeRange { result, .. }
        | IntegerArithmeticNode::OperationBound { result, .. }
        | IntegerArithmeticNode::ExcludedTypeBound { result, .. }
        | IntegerArithmeticNode::StrictFromDisequal { result, .. } => result,
    }
}

fn contradiction_claim(claim: &IntegerAffineClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            IntegerAffineRelation::LessEqual => claim.constant > BigInt::zero(),
            IntegerAffineRelation::Equal => !claim.constant.is_zero(),
        }
}

/// Restate one relation by explicitly proved identities of its operands.
/// There is no affine reasoning over facts hidden in `normalize using`:
/// all the algebra is in the two context-free identity goals.
fn transfer(target: &SyntaxProposition, fact: &SyntaxProposition) -> Vec<ProofStep> {
    let (a, operator, b) = integer_surface_ordered_parts(target).expect("composition target");
    let (c, _, d) = integer_surface_ordered_parts(fact).expect("composition fact");
    let left = compare(a.clone(), true, c.clone());
    let right = compare(b.clone(), true, d.clone());
    let mut body = Vec::new();
    if a != c {
        body.push(computational_fact(left.clone()));
    }
    if b != d {
        body.push(computational_fact(right.clone()));
    }
    body.push(application(
        if operator == ComparisonOperator::Equal {
            "equal_substitute"
        } else {
            "le_substitute"
        },
        vec![c, d, a, b],
        vec![fact.clone(), left, right],
    ));
    body
}

fn with_argument_domains(step: ProofStep, domains: &[SyntaxProposition]) -> ProofStep {
    match step {
        ProofStep::Have { proposition, proof } => have(
            proposition,
            proof
                .steps()
                .iter()
                .cloned()
                .map(|step| with_argument_domains(step, domains))
                .collect(),
        ),
        ProofStep::ApplyPlannedTheorem {
            application,
            mut premises,
        } => {
            premises.extend(
                domains
                    .iter()
                    .filter(|domain| !premises.contains(domain))
                    .cloned()
                    .collect::<Vec<_>>(),
            );
            ProofStep::ApplyPlannedTheorem {
                application,
                premises,
            }
        }
        other => other,
    }
}

pub(super) fn observed_argument(expression: &SyntaxTerm) -> Option<SyntaxTerm> {
    match expression {
        SyntaxTerm::IntegerContext(value) => observed_argument(value),
        SyntaxTerm::Call { name, arguments } if name == "to_integer" && arguments.len() == 1 => {
            observed_argument(&arguments[0]).or_else(|| Some(arguments[0].clone()))
        }
        SyntaxTerm::At {
            selector,
            expression,
        } => Some(SyntaxTerm::At {
            selector: selector.clone(),
            expression: Box::new(observed_argument(expression)?),
        }),
        SyntaxTerm::Old(expression) => {
            Some(SyntaxTerm::Old(Box::new(observed_argument(expression)?)))
        }
        SyntaxTerm::Let {
            name,
            click_type: Some(ClickType::Integer),
            value,
            body,
        } if matches!(body.as_ref(), SyntaxTerm::Binding(bound) if bound == name) => {
            observed_argument(value)
        }
        _ => None,
    }
}

fn run_scope<'a>(
    mut scope: super::super::proof_object::ProofScope<'a>,
    steps: &[ProofStep],
) -> Result<super::super::proof_object::ProofScope<'a>, ClickError> {
    if steps.is_empty() && !scope.is_complete() {
        if scope
            .body()
            .goal()
            .is_some_and(crate::kernel::proof::fact_reasoning::computes_leaf)
        {
            return scope.driver().apply_step(ProofStep::Known);
        }
        return scope.driver().try_integer_algebra()?.ok_or_else(|| {
            scope
                .body()
                .step_error("integer composition could not prove a local identity")
        });
    }
    for step in steps {
        if scope.is_complete() {
            break;
        }
        match step {
            ProofStep::Have { proposition, proof } => {
                let nested = scope.driver().open_have(proposition.clone())?;
                let closed = run_scope(nested, proof.steps())?;
                scope = scope.join_nested(closed)?;
            }
            step => scope = scope.driver().apply_step(step.clone())?,
        }
    }
    if scope.is_complete() {
        Ok(scope)
    } else {
        scope.driver().apply_step(ProofStep::Known)
    }
}

#[cfg(test)]
thread_local! {
    static LAST_FAILURE: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

/// Whether a definedness range bound is an established fact. The domain
/// query states its lower bound as `exact >= MIN`, while a proved bound
/// written `MIN <= exact` lowers to the reversed comparison; both are the
/// same fact, so either exact key counts.
fn range_bound_available(proof: &Proof<'_>, bound: &Proposition) -> bool {
    let facts = proof.facts();
    if facts.listed_premise_available(bound, &[], false) {
        return true;
    }
    let reversed = match bound {
        Proposition::ConditionIs(condition, value) => match condition.old_form() {
            OldConditionTerm::IntegerGreaterEqual(left, right) => Proposition::condition_is(
                OldConditionTerm::IntegerLessEqual(right.clone(), left.clone()),
                *value,
            ),
            OldConditionTerm::IntegerLessEqual(left, right) => Proposition::condition_is(
                OldConditionTerm::IntegerGreaterEqual(right.clone(), left.clone()),
                *value,
            ),
            _ => return false,
        },
        _ => return false,
    };
    facts.listed_premise_available(&reversed, &[], false)
}

#[cfg(test)]
pub(super) fn note_refusal(message: impl Into<String>) {
    let message = message.into();
    LAST_FAILURE.with(|failure| *failure.borrow_mut() = Some(message));
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Close an impossible branch by establishing the selected fact's
    /// opposite. Only the written comparison enters the algebra planner.
    pub(in crate::surface::proof) fn close_refuted_fact(
        proof: &Proof<'a>,
        fact: &SyntaxProposition,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("close_refuted_fact");
        if proof.facts().holds_false() {
            return proof.driver().apply_step(ProofStep::Known);
        }
        let scope = proof
            .driver()
            .open_have(SyntaxProposition::Not(Box::new(fact.clone())))?;
        let proved = match attempt::candidate_outcome(scope.driver().apply_step(ProofStep::Known))?
        {
            Some(closed) => closed,
            // The plan can reduce to a constant while its written
            // operands still contain products and anchored values.
            None => scope.driver().try_integer_algebra()?.ok_or_else(|| {
                proof.step_error("could not prove the negation of the selected fact")
            })?,
        };
        let refuted = proved.join()?;
        refuted.driver().apply_step(ProofStep::Known)
    }

    /// Refute an equality with one listed constant bound. Keeping the
    /// substitution explicit also preserves machine observations in the bound.
    pub(super) fn try_interval_exclusion_using(
        input: &Proof<'a>,
        premises: &[(Proposition, SyntaxProposition)],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_interval_exclusion_using");
        let Some(SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::NotEqual,
            right,
        }) = input.surface_goal().and_then(canonical_surface)
        else {
            return Ok(None);
        };
        let equality = compare(left.clone(), true, right.clone());
        let kernel = input.lower_integer_surface_proposition(&equality, "excluded equality")?;
        let Some(Reading {
            left: a,
            right: b,
            equal: true,
            ..
        }) = reading(&kernel)
        else {
            return Ok(None);
        };
        let (term, excluded) = match (a.as_const(), b.as_const()) {
            (None, Some(value)) => (&a, value),
            (Some(value), None) => (&b, value),
            _ => return Ok(None),
        };
        for (premise, surface) in premises {
            check_verification_deadline()?;
            let Some(Reading {
                left: lo,
                right: hi,
                equal: false,
                strict: false,
            }) = reading(premise)
            else {
                continue;
            };
            let Some((endpoint, lower)) = (if &hi == term {
                lo.as_const().map(|value| (value, true))
            } else if &lo == term {
                hi.as_const().map(|value| (value, false))
            } else {
                None
            }) else {
                continue;
            };
            if crate::instrumentation::deadline_exceeded_with_work(
                usize::try_from(endpoint.bits().saturating_add(excluded.bits()))
                    .unwrap_or(usize::MAX),
            ) {
                return Ok(None);
            }
            if (lower && excluded >= endpoint) || (!lower && excluded <= endpoint) {
                continue;
            }
            let Some(term) =
                input.spell_written_integer_observation(term, &[left.clone(), right.clone()])
            else {
                continue;
            };
            let endpoint = literal(endpoint);
            let excluded = literal(excluded);
            let (a, b, c, d) = if lower {
                (endpoint.clone(), term, endpoint, excluded)
            } else {
                (term, endpoint.clone(), excluded, endpoint)
            };
            let impossible = compare(c.clone(), false, d.clone());
            let substitution = application(
                "le_substitute",
                vec![a.clone(), b.clone(), c.clone(), d.clone()],
                vec![surface.clone(), compare(c, true, a), compare(d, true, b)],
            );
            let (proof, split, ids) = input.split_focused_if(equality.clone())?;
            let marker = proof.checkpoint();
            let equal_arm = proof.focus_branch(ids[0])?;
            let scope = equal_arm.driver().open_have(impossible.clone())?;
            let refuted = scope.driver().apply_step_then_close(substitution)?.join()?;
            let equal_done = Self::close_refuted_fact(&refuted, &impossible)?;
            let unequal_done = equal_done
                .focus_branch(ids[1])?
                .driver()
                .apply_step(ProofStep::Known)?;
            return unequal_done
                .join_focused_if(&marker, split, ids, equality)
                .map(Some);
        }
        Ok(None)
    }

    pub(in crate::surface::proof) fn apply_integer_composition(
        proof: &Proof<'a>,
        plan: &IntegerArithmeticPlan,
        pairs: &[(Proposition, SyntaxProposition)],
        surface_goal: &SyntaxProposition,
        ranges: &[SpelledBound],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_integer_composition");
        let Some(goal) = proof.goal() else {
            return Ok(None);
        };
        for (kernel, surface) in pairs {
            if normalizes_context_free(&Proposition::Not(Box::new(kernel.clone())))
                && let Some(closed) =
                    attempt::candidate_outcome(Self::close_refuted_fact(proof, surface))?
            {
                return Ok(Some(closed));
            }
        }
        let observed_goal = observed_native_surface_comparison(goal, surface_goal);
        let goal_surface = canonical_surface(&observed_goal);
        // A resource or typed expression can introduce a scalar obligation
        // without a written comparison. Its ordinary proof concludes the
        // plan's named linear form directly, rather than inventing a source
        // comparison for that generated obligation.
        let goal_kernel = if goal_surface.is_some() {
            proof.lower_cited_surface_proposition(&observed_goal, "Integer composition goal")?
        } else {
            goal.clone()
        };
        let claims = crate::kernel::proof::integer_arithmetic::integer_affine_claims(&goal_kernel);
        let Some(expected) = claims
            .iter()
            .find(|claim| *claim == node_claim(&plan.nodes[plan.conclusion]))
            .or(claims.first())
            .cloned()
        else {
            return Ok(None);
        };
        let goal_reading = reading_matching(&goal_kernel, &expected);
        let direct = direct_refutation(plan, &expected);
        let plan = direct.as_ref().unwrap_or(plan);
        let contradictory = contradiction_claim(node_claim(&plan.nodes[plan.conclusion]));
        if node_claim(&plan.nodes[plan.conclusion]) != &expected && !contradictory {
            #[cfg(test)]
            note_refusal(format!(
                "plan result {:?}, observed goal {:?}",
                node_claim(&plan.nodes[plan.conclusion]),
                expected
            ));
            return Ok(None);
        }
        let mut uses_negated_goal = false;
        let mut used = BTreeSet::new();
        let mut used_premises = BTreeSet::new();
        let mut pending = vec![plan.conclusion];
        while let Some(index) = pending.pop() {
            if !used.insert(index) {
                continue;
            }
            let Some(node) = plan.nodes.get(index) else {
                return Ok(None);
            };
            match node {
                IntegerArithmeticNode::Premise { index, .. } => {
                    used_premises.insert(*index);
                    if pairs.get(*index).is_none() {
                        return Ok(None);
                    }
                }
                IntegerArithmeticNode::Scale { source, .. }
                | IntegerArithmeticNode::EqualityToLessEqual { source, .. } => {
                    pending.push(*source)
                }
                IntegerArithmeticNode::Add { left, right, .. } => pending.extend([*left, *right]),
                IntegerArithmeticNode::EqualityFromBounds { lower, upper, .. } => {
                    pending.extend([*lower, *upper])
                }
                IntegerArithmeticNode::StrictFromDisequal {
                    bound, disequal, ..
                } => {
                    pending.push(*bound);
                    used_premises.insert(*disequal);
                }
                IntegerArithmeticNode::ExcludedTypeBound { index, .. } => {
                    used_premises.insert(*index);
                }
                IntegerArithmeticNode::NegatedGoal { .. } => uses_negated_goal = true,

                _ => {}
            }
        }
        let owned_ranges;
        let ranges = if ranges.is_empty()
            && used.iter().any(|index| {
                matches!(
                    plan.nodes[*index],
                    IntegerArithmeticNode::TypeRange { .. }
                        | IntegerArithmeticNode::OperationBound { .. }
                        | IntegerArithmeticNode::ExcludedTypeBound { .. }
                )
            }) {
            let written = written_integer_observations(
                std::iter::once(surface_goal).chain(pairs.iter().map(|(_, surface)| surface)),
            );
            let mut spelled = proof
                .spell_type_ranges(plan, &written)
                .map_err(|_| proof.step_error("Integer type range has no source spelling"))?;
            let kernels = pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            spelled.extend(
                proof
                    .spell_derived_bounds(plan, &kernels, &written)
                    .ok_or_else(|| {
                        proof.step_error("Integer operation bound has no source spelling")
                    })?,
            );
            owned_ranges = spelled;
            owned_ranges.as_slice()
        } else {
            ranges
        };
        let mut atoms = BTreeMap::new();
        let mut nodes: BTreeMap<usize, Node> = BTreeMap::new();
        let mut steps = Vec::new();
        for index in used {
            check_verification_deadline()?;
            let (form, equal, body) = match &plan.nodes[index] {
                IntegerArithmeticNode::Premise { index, result } => {
                    let (kernel, source) = &pairs[*index];
                    let observed = observed_native_surface_comparison(kernel, source);
                    let lowered = proof.lower_cited_surface_proposition(
                        &observed,
                        "Integer composition premise",
                    )?;
                    let Some(relation) = reading_matching(&lowered, result) else {
                        #[cfg(test)]
                        note_refusal(format!("unsupported observed source: {lowered:?}"));
                        return Ok(None);
                    };
                    let Some(canonical) = canonical_surface(&observed) else {
                        return Ok(None);
                    };
                    prepare_relation(relation, &canonical, source, &mut atoms)
                }
                IntegerArithmeticNode::NegatedGoal { .. } => {
                    let source = SyntaxProposition::Not(Box::new(surface_goal.clone()));
                    let kernel = Proposition::Not(Box::new(goal.clone()));
                    let observed = observed_native_surface_comparison(&kernel, &source);
                    let lowered =
                        proof.lower_cited_surface_proposition(&observed, "Integer negated goal")?;
                    let Some(relation) = reading_matching(&lowered, node_claim(&plan.nodes[index]))
                    else {
                        #[cfg(test)]
                        note_refusal(format!("unsupported observed source: {lowered:?}"));
                        return Ok(None);
                    };
                    let Some(canonical) = canonical_surface(&observed) else {
                        return Ok(None);
                    };
                    prepare_relation(relation, &canonical, &source, &mut atoms)
                }
                IntegerArithmeticNode::TypeRange { value, upper, .. }
                | IntegerArithmeticNode::OperationBound { value, upper, .. } => {
                    let kind =
                        if matches!(&plan.nodes[index], IntegerArithmeticNode::TypeRange { .. }) {
                            BoundSource::TypeRange
                        } else {
                            BoundSource::Operation
                        };
                    let Some(source) = spelled_bound(ranges, kind, value, *upper) else {
                        return Ok(None);
                    };
                    let lowered = proof
                        .lower_cited_surface_proposition(&source, "Integer intrinsic bound")?;
                    let Some(relation) = reading_matching(&lowered, node_claim(&plan.nodes[index]))
                    else {
                        #[cfg(test)]
                        note_refusal(format!("unsupported observed source: {lowered:?}"));
                        return Ok(None);
                    };
                    let Some(canonical) = canonical_surface(&source) else {
                        return Ok(None);
                    };
                    let (form, equal, mut body) =
                        prepare_relation(relation, &canonical, &source, &mut atoms);
                    body.insert(0, have(source, vec![ProofStep::Known]));
                    (form, equal, body)
                }
                IntegerArithmeticNode::StrictFromDisequal {
                    bound, disequal, ..
                } => strict_node(proof, &nodes[bound], &pairs[*disequal], &mut atoms)?,
                IntegerArithmeticNode::ExcludedTypeBound { index: premise, .. } => {
                    let source = ranges
                        .iter()
                        .find(|(kind, ..)| *kind == BoundSource::Excluded(*premise))
                        .map(|(.., surface)| surface)
                        .ok_or_else(|| proof.step_error("excluded type bound has no spelling"))?;
                    let kernel =
                        proof.lower_cited_surface_proposition(source, "excluded type bound")?;
                    let relation = reading(&kernel).expect("excluded bound is ordered");
                    let (left, _, right) =
                        integer_surface_ordered_parts(source).expect("excluded bound spelling");
                    let (base_kernel, base_surface) =
                        if let Some(min_plus_one) = relation.left.as_const() {
                            let min = min_plus_one - BigInt::one();
                            (
                                Proposition::condition_is(
                                    OldConditionTerm::IntegerLessEqual(
                                        IntegerTerm::constant(min.clone()).into(),
                                        relation.right,
                                    ),
                                    true,
                                ),
                                compare(literal(&min), false, right),
                            )
                        } else {
                            let max =
                                relation.right.as_const().expect("upper endpoint") + BigInt::one();
                            (
                                Proposition::condition_is(
                                    OldConditionTerm::IntegerLessEqual(
                                        relation.left,
                                        IntegerTerm::constant(max.clone()).into(),
                                    ),
                                    true,
                                ),
                                compare(left, false, literal(&max)),
                            )
                        };
                    let (form, equal, mut base_body) = prepare_relation(
                        reading(&base_kernel).unwrap(),
                        &base_surface,
                        &base_surface,
                        &mut atoms,
                    );
                    base_body.insert(0, have(base_surface, vec![ProofStep::Known]));
                    let base_claim = compare(expression(&form, &atoms), false, zero());
                    let base = Node {
                        form,
                        equal,
                        claim: base_claim.clone(),
                        semantic: integer_affine_claim(&base_kernel).unwrap(),
                    };
                    let (form, equal, mut body) =
                        strict_node(proof, &base, &pairs[*premise], &mut atoms)?;
                    body.insert(0, have(base_claim, base_body));
                    (form, equal, body)
                }

                IntegerArithmeticNode::Scale {
                    source,
                    coefficient,
                    ..
                } => {
                    let source = &nodes[source];
                    let form = source.form.scaled(coefficient);
                    let factor = literal(coefficient);
                    let raw = multiply(expression(&source.form, &atoms), factor.clone());
                    let target = compare(expression(&form, &atoms), source.equal, zero());
                    let mut body = Vec::new();
                    let fact = if source.equal {
                        let fact = compare(raw, true, multiply(zero(), factor.clone()));
                        body.push(have(
                            fact.clone(),
                            vec![application(
                                "equal_multiply",
                                vec![expression(&source.form, &atoms), zero(), factor.clone()],
                                vec![source.claim.clone()],
                            )],
                        ));
                        fact
                    } else {
                        let positive = compare(zero(), false, factor.clone());
                        body.push(computational_fact(positive.clone()));
                        let fact = compare(raw, false, multiply(zero(), factor.clone()));
                        body.push(have(
                            fact.clone(),
                            vec![application(
                                "multiply_order_nonnegative",
                                vec![expression(&source.form, &atoms), zero(), factor],
                                vec![source.claim.clone(), positive],
                            )],
                        ));
                        fact
                    };
                    body.extend(transfer(&target, &fact));
                    (form, source.equal, body)
                }
                IntegerArithmeticNode::Add { left, right, .. } => {
                    let (left, right) = (&nodes[left], &nodes[right]);
                    let form = left.form.add(&right.form);
                    let raw = add(
                        expression(&left.form, &atoms),
                        expression(&right.form, &atoms),
                    );
                    let target = compare(expression(&form, &atoms), left.equal, zero());
                    let fact = compare(raw, left.equal, add(zero(), zero()));
                    let body = if left.equal {
                        vec![application(
                            "equal_add",
                            vec![
                                expression(&left.form, &atoms),
                                zero(),
                                expression(&right.form, &atoms),
                                zero(),
                            ],
                            vec![left.claim.clone(), right.claim.clone()],
                        )]
                    } else {
                        vec![application(
                            "add_le",
                            vec![
                                expression(&left.form, &atoms),
                                zero(),
                                expression(&right.form, &atoms),
                                zero(),
                            ],
                            vec![left.claim.clone(), right.claim.clone()],
                        )]
                    };
                    let mut body = vec![have(fact.clone(), body)];
                    body.extend(transfer(&target, &fact));
                    (form, left.equal, body)
                }
                IntegerArithmeticNode::EqualityToLessEqual {
                    source, reverse, ..
                } => {
                    let source = &nodes[source];
                    let form = source
                        .form
                        .scaled(&BigInt::from(if *reverse { -1 } else { 1 }));
                    let value = expression(&form, &atoms);
                    let equal = compare(value.clone(), true, zero());
                    let mut body = Vec::new();
                    if *reverse {
                        let source_value = expression(&source.form, &atoms);
                        // Keep the sign change additive. The law's conclusion
                        // has unary negation of Integer zero, which the literal
                        // spelling `-0` would lower to a constant.
                        let integer_zero =
                            super::super::surface_synthesis::integer_typed_expression(zero());
                        let fact = compare(
                            SyntaxTerm::Negate(Box::new(source_value.clone())),
                            true,
                            SyntaxTerm::Negate(Box::new(integer_zero)),
                        );
                        body.push(have(
                            fact.clone(),
                            vec![application(
                                "equal_negate",
                                vec![source_value, zero()],
                                vec![source.claim.clone()],
                            )],
                        ));
                        body.push(have(equal.clone(), transfer(&equal, &fact)));
                    }
                    body.push(application("equal_le", vec![value, zero()], vec![equal]));
                    (form, false, body)
                }
                IntegerArithmeticNode::EqualityFromBounds { lower, upper, .. } => {
                    let (lower, upper) = (&nodes[lower], &nodes[upper]);
                    let form = lower.form.clone();
                    let value = expression(&form, &atoms);
                    let reflexive = compare(value.clone(), false, value.clone());
                    let fact = compare(
                        add(expression(&upper.form, &atoms), value.clone()),
                        false,
                        add(zero(), value.clone()),
                    );
                    let opposite = compare(zero(), false, value.clone());
                    let mut body = vec![
                        computational_fact(reflexive.clone()),
                        have(
                            fact.clone(),
                            vec![application(
                                "add_le",
                                vec![
                                    expression(&upper.form, &atoms),
                                    zero(),
                                    value.clone(),
                                    value.clone(),
                                ],
                                vec![upper.claim.clone(), reflexive],
                            )],
                        ),
                    ];
                    body.push(have(opposite.clone(), transfer(&opposite, &fact)));
                    body.push(application(
                        "le_antisymmetric",
                        vec![value, zero()],
                        vec![lower.claim.clone(), opposite],
                    ));
                    (form, true, body)
                }
                IntegerArithmeticNode::Trivial { result } => (
                    Form {
                        constant: result.constant.clone(),
                        ..Form::default()
                    },
                    result.relation == IntegerAffineRelation::Equal,
                    vec![ProofStep::Known],
                ),
            };
            let claim = compare(expression(&form, &atoms), equal, zero());
            steps.push(have(claim.clone(), body));
            nodes.insert(
                index,
                Node {
                    form,
                    equal,
                    claim,
                    semantic: node_claim(&plan.nodes[index]).clone(),
                },
            );
        }
        let conclusion = &nodes[&plan.conclusion];
        let refuted_fact = if contradictory {
            Some(conclusion.claim.clone())
        } else if goal_surface.is_none() {
            steps.push(have(
                SyntaxProposition::Not(Box::new(conclusion.claim.clone())),
                vec![ProofStep::Known],
            ));
            Some(conclusion.claim.clone())
        } else {
            let (Some(relation), Some(canonical)) = (goal_reading, goal_surface) else {
                return Ok(None);
            };
            let (left, _, right) =
                integer_surface_non_strict_parts(&canonical).expect("ordered goal");
            let non_strict = compare(left, relation.equal, right);
            steps.extend(restore(&canonical, conclusion, &atoms));
            if relation.strict {
                let (left, _, right) =
                    integer_surface_ordered_parts(&canonical).expect("strict goal");
                steps.push(application(
                    "step_le_lt",
                    vec![left, right],
                    vec![non_strict],
                ));
            }
            if uses_negated_goal {
                Some(surface_goal.clone())
            } else {
                steps = vec![have(canonical.clone(), steps), ProofStep::Known];
                None
            }
        };
        // The theorem's arguments can contain partial native operations.
        // Cite their already established domains explicitly, so the simple
        // using checker sees the same argument evidence during replay.
        let written = written_integer_observations(
            std::iter::once(surface_goal).chain(
                pairs
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| used_premises.contains(index))
                    .map(|(_, (_, surface))| surface),
            ),
        );
        let mut domain_candidates = Vec::new();
        for expression in &written {
            if let Some(expression) = observed_argument(expression) {
                domain_candidates.push(SyntaxProposition::Defined { expression });
            }
        }
        // Partial mathematical operations and native arguments of opaque
        // Integer calls keep their evaluation obligations when used as law
        // arguments. Collect those obligations from the same written terms.
        let mut terms = Vec::new();
        collect_signed_surface_proposition_terms(surface_goal, &mut terms);
        for index in &used_premises {
            collect_signed_surface_proposition_terms(&pairs[*index].1, &mut terms);
        }
        for term in terms {
            match term {
                SyntaxTerm::Call { name, arguments }
                    if matches!(
                        name.as_str(),
                        "truncating_quotient" | "truncating_remainder"
                    ) && arguments.len() == 2 =>
                {
                    domain_candidates.push(SyntaxProposition::Comparison {
                        left: arguments[1].clone(),
                        operator: ComparisonOperator::NotEqual,
                        right: SyntaxTerm::IntegerLiteral("0".into()),
                    });
                }
                SyntaxTerm::Add(_, _)
                | SyntaxTerm::Subtract(_, _)
                | SyntaxTerm::Multiply(_, _)
                | SyntaxTerm::Divide(_, _)
                | SyntaxTerm::Remainder(_, _)
                | SyntaxTerm::ShiftLeft(_, _)
                | SyntaxTerm::ShiftRight(_, _)
                | SyntaxTerm::BitwiseAnd(_, _)
                | SyntaxTerm::CUnary { .. }
                | SyntaxTerm::MemoryLoad { .. }
                | SyntaxTerm::ProgramExpression(
                    ProgramExpression::Add(..)
                    | ProgramExpression::Subtract(..)
                    | ProgramExpression::Multiply(..)
                    | ProgramExpression::Divide(..)
                    | ProgramExpression::Remainder(..)
                    | ProgramExpression::ShiftLeft(..)
                    | ProgramExpression::ShiftRight(..)
                    | ProgramExpression::BitwiseAnd(..)
                    | ProgramExpression::Cast { .. },
                ) => {
                    domain_candidates.push(SyntaxProposition::Defined {
                        expression: term.clone(),
                    });
                }
                _ => {}
            }
        }
        let mut prepared = proof.clone();
        let mut domains = Vec::new();
        let mut domain_proofs = Vec::new();
        let mut considered_domains = std::collections::HashSet::new();
        // Spellings of one domain, such as `defined(hi - 1)`, its cast
        // `defined((hi - 1) as int32)`, or `old(...)` in a pure proof, lower
        // to the same fact. Once one spelling establishes it, cite that one
        // and skip the rest. A spelling that declined leaves the fact open.
        let mut established_kernels = std::collections::HashSet::new();
        let mut pending: Option<(usize, Proposition)> = None;
        for domain in domain_candidates {
            if let Some((count, kernel)) = pending.take()
                && domains.len() > count
            {
                established_kernels.insert(kernel);
            }
            if !considered_domains.insert(domain.clone()) {
                continue;
            }
            // Synthetic observations of an Integer are not native domains.
            let Ok(kernel) =
                prepared.lower_cited_surface_proposition(&domain, "Integer argument domain")
            else {
                continue;
            };
            if established_kernels.contains(&kernel) {
                continue;
            }
            pending = Some((domains.len(), kernel.clone()));
            // The signed-definedness search below serves a range domain whose
            // operands owe nothing. A candidate whose operand is itself an
            // operation or a read is kept only when it closes directly: the
            // theorem's own arguments carry that operand's domain.
            let Some(query) = (!domain_has_compound_operand(&domain))
                .then(|| crate::kernel::machine_integer::definedness::range_domain_query(&kernel))
                .flatten()
            else {
                // Reads can carry a separate domain as well. Retain that
                // exact established fact for theorem-argument checking.
                if !normalizes_context_free(&kernel)
                    && prepared
                        .facts()
                        .listed_premise_available(&kernel, &[], false)
                    && !domains.contains(&domain)
                {
                    domain_proofs.push(have(domain.clone(), vec![ProofStep::Known]));
                    domains.push(domain.clone());
                }
                if matches!(domain, SyntaxProposition::Defined { .. })
                    && !normalizes_context_free(&kernel)
                    && !domains.contains(&domain)
                {
                    let scope = prepared.driver().open_have(domain.clone())?;
                    if let Some(closed) = scope.driver().try_direct_logical_closure()? {
                        prepared = closed.join()?;
                        domains.push(domain);
                    }
                }
                continue;
            };
            if domains.contains(&domain) {
                continue;
            }
            if prepared
                .facts()
                .listed_premise_available(&kernel, &[], false)
            {
                domain_proofs.push(have(domain.clone(), vec![ProofStep::Known]));
            } else if let Proposition::And(left, right) = &kernel
                && query
                    .bounds()
                    .iter()
                    .all(|bound| range_bound_available(&prepared, bound))
            {
                let conjuncts =
                    [left, right].map(|bound| prepared.conjunct_goal_spelling(bound).map(Arc::new));
                domain_proofs.push(have(
                    domain.clone(),
                    vec![ProofStep::Both {
                        conjuncts,
                        left_proof: Box::new(ProofCertificate::from_validated_steps(vec![
                            ProofStep::Known,
                        ])),
                        right_proof: Box::new(ProofCertificate::from_validated_steps(vec![
                            ProofStep::Known,
                        ])),
                    }],
                ));
            } else {
                // The native argument may have been evaluated under bounds
                // without its domain being retained as a separate fact. Prove
                // that domain through the same ordinary definedness route.
                let scope = prepared.driver().open_have(domain.clone())?;
                let Some(closed) = scope.driver().try_signed_definedness_closure()? else {
                    continue;
                };
                prepared = closed.join()?;
            }
            domains.push(domain);
        }
        if !domains.is_empty() {
            steps = steps
                .into_iter()
                .map(|step| with_argument_domains(step, &domains))
                .collect();
        }
        let apply =
            |mut result: Proof<'a>, steps: Vec<ProofStep>| -> Result<Proof<'a>, ClickError> {
                for step in steps {
                    if result.focused_discharged() {
                        break;
                    }
                    let next = match step {
                        ProofStep::Have { proposition, proof } => {
                            let scope = result.driver().open_have(proposition)?;
                            run_scope(scope, proof.steps()).and_then(|scope| scope.join())
                        }
                        step => result.driver().apply_step(step),
                    };
                    #[cfg(test)]
                    if let Err(error) = &next {
                        LAST_FAILURE.with(|failure| {
                            *failure.borrow_mut() = Some(error.raw_summary().to_owned());
                        });
                    }
                    result = next?;
                }
                Ok(result)
            };
        let prepared = apply(prepared, domain_proofs)?;
        if prepared.focused_discharged() {
            return Ok(Some(prepared));
        }
        let finish = |branch: Proof<'a>| {
            if branch.focused_discharged() {
                return Ok(branch);
            }
            match &refuted_fact {
                Some(fact) => Self::close_refuted_fact(&branch, fact),
                None => branch.driver().apply_step(ProofStep::Known),
            }
        };
        let result = if uses_negated_goal {
            let (proof, split, ids) = prepared.split_focused_if(surface_goal.clone())?;
            let marker = proof.checkpoint();
            let positive = proof
                .focus_branch(ids[0])?
                .driver()
                .apply_step(ProofStep::Known)?;
            let negative = finish(apply(positive.focus_branch(ids[1])?, steps)?)?;
            negative.join_focused_if(&marker, split, ids, surface_goal.clone())?
        } else {
            finish(apply(prepared, steps)?)?
        };
        if !result.focused_discharged() {
            return Err(result.step_error("Integer composition did not close the written goal"));
        }
        Ok(Some(result))
    }
}

#[cfg(test)]
mod tests {
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };

    use super::*;
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    use crate::surface::proof::pure_theorems::PureTheoremContext;

    pub(super) fn shared_plan(
        depth: usize,
        ambient: usize,
        related: bool,
    ) -> (usize, usize, usize) {
        let x: SharedIntegerTerm = IntegerTerm::Variable(Variable(871_001)).into();
        let y: SharedIntegerTerm = IntegerTerm::Variable(Variable(871_002)).into();
        let z: SharedIntegerTerm = IntegerTerm::Variable(Variable(871_003)).into();
        let premise = Proposition::condition_is(
            OldConditionTerm::IntegerLessEqual(x.clone(), y.clone()),
            true,
        );
        let surface = compare(
            SyntaxTerm::Binding("x".into()),
            false,
            SyntaxTerm::Binding("y".into()),
        );
        let mut context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            point: crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
            values: ProgramValueBindings::new(),
            integer_values: PersistentBinderMap::default(),
            array_refs: BTreeMap::new(),
            requires: vec![premise.clone()],
            surface_requirements: SurfacePropositionMap::default(),
        };
        for (name, term) in [("x", &x), ("y", &y), ("z", &z)] {
            context.integer_values = context
                .integer_values
                .with_inserted(name, SpecIntegerExpression::Term(term.as_ref().clone()));
        }
        for index in 1..=ambient {
            context.requires.push(Proposition::condition_is(
                OldConditionTerm::IntegerLessEqual(
                    if related { x.clone() } else { z.clone() },
                    if related {
                        IntegerTerm::add(
                            y.as_ref().clone(),
                            IntegerTerm::constant_i64(index as i64),
                        )
                        .into()
                    } else {
                        IntegerTerm::constant_i64(index as i64).into()
                    },
                ),
                true,
            ));
        }
        let mut claim = integer_affine_claim(&premise).unwrap();
        let mut nodes = vec![IntegerArithmeticNode::Premise {
            index: 0,
            result: claim.clone(),
        }];
        for source in 0..depth {
            for coefficient in claim.terms.values_mut() {
                *coefficient *= 2;
            }
            claim.constant *= 2;
            nodes.push(IntegerArithmeticNode::Add {
                left: source,
                right: source,
                result: claim.clone(),
            });
        }
        let factor = BigInt::one() << depth;
        let goal = Proposition::condition_is(
            OldConditionTerm::IntegerLessEqual(
                IntegerTerm::multiply(IntegerTerm::Constant(factor.clone()), x.as_ref().clone())
                    .into(),
                IntegerTerm::multiply(IntegerTerm::Constant(factor.clone()), y.as_ref().clone())
                    .into(),
            ),
            true,
        );
        let surface_goal = compare(
            multiply(literal(&factor), SyntaxTerm::Binding("x".into())),
            false,
            multiply(literal(&factor), SyntaxTerm::Binding("y".into())),
        );
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let file = crate::surface::parse("").unwrap();
        let definitions = proof_theorem_definitions(&file).unwrap();
        let theorems = TheoremEnvironment::new(&definitions);
        let root = Proof::for_pure_surface_goal(
            "composition sharing",
            &context.requires,
            goal,
            surface_goal.clone(),
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let plan = IntegerArithmeticPlan {
            nodes,
            conclusion: depth,
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::apply_integer_composition(
                &root,
                &plan,
                &[(premise, surface)],
                &surface_goal,
                &[],
            )
        });
        let result = result
            .unwrap_or_else(|error| panic!("{}", error.message()))
            .expect("the shared plan is supported");
        assert!(result.is_complete());
        let certificate = result.certificate();
        let printed = format!("{:?}", certificate.steps());
        assert!(!printed.contains("ArithmeticCertificate"));
        (work, printed.len(), certificate.steps().len())
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: shared-plan construction takes 0.6s in parallel"]
    fn integer_composition_shared_plan_constructs_each_node_once() {
        let (_, _, steps) = shared_plan(2, 0, false);
        assert!(
            steps <= 2 + 8,
            "shared derivations became nested proof copies: {steps}"
        );
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn integer_composition_keeps_algebraic_arguments_and_integer_aliases() {
        let source = r#"
            function weight(xs: List<int32>) -> Integer { 0 }
            theorem composition(xs: List<int32>) {
                requires weight(xs) >= 0;
                ensures (let value: Integer = weight(xs) + 1; value) >= 0 by {
                    close() using { weight(xs) >= 0; };
                }
            }
        "#;
        let expanded = expand_c_claim_source_by_label(source, &[], "composition.ensures_0")
            .unwrap_or_else(|error| panic!("{}", error.message()));
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }

    macro_rules! composition_case {
        ($(#[$meta:meta])* $name:ident, $parameters:literal, $requirements:literal, $goal:literal) => {
            #[test]
            $(#[$meta])*
            fn $name() {
                let source = format!(
                    "theorem composition({}) {{ {} ensures {} by {{ close() using {{ {} }}; }} }}",
                    $parameters,
                    $requirements,
                    $goal,
                    $requirements.replace("requires ", "")
                );
                let expanded =
                    expand_c_claim_source_by_label(&source, &[], "composition.ensures_0")
                        .unwrap_or_else(|error| panic!("{}", error.message()));
                assert!(!expanded.contains("normalize("), "{expanded}");
                assert!(!expanded.contains("solve("), "{expanded}");
                without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                    .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
            }
        };
    }
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_strict_premise,
        "x: Integer, y: Integer",
        "requires x < y;",
        "2 * x + 2 <= 2 * y"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_strict_goal,
        "x: Integer, y: Integer",
        "requires x + 1 <= y;",
        "x < y"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_negative_premise,
        "x: Integer",
        "requires not (x <= 3);",
        "4 <= x"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_strict_disequality,
        "x: Integer, y: Integer",
        "requires x <= y; requires x != y;",
        "x < y"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_refutation_chain,
        "a: Integer, b: Integer, c: Integer, d: Integer, e: Integer",
        "requires a <= b; requires b <= c; requires c <= d; requires d <= e;",
        "a <= e"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_rounding,
        "x: Integer",
        "requires 2 * x <= 5;",
        "x <= 2"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_native_bridge,
        "x: uint64",
        "requires x <= 5u64;",
        "2 * to_integer(x) <= 10"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_intrinsic_range,
        "x: int64",
        "",
        "-9223372036854775808 <= to_integer(x)"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_intrinsic_quotient,
        "x: uint64",
        "",
        "4 * to_integer(x / 4u64) <= to_integer(x)"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_excluded_endpoint,
        "x: uint64",
        "requires x != 0u64;",
        "0u64 < x"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: minimal scaled-bound expansion and replay took 2.1s in parallel"]
        integer_composition_single_scaled_bound,
        "x: Integer",
        "requires x <= 3;",
        "2 * x <= 6"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: ordinary expansion and replay take 0.6s in parallel"]
        integer_composition_scaled_sum,
        "x: Integer, y: Integer",
        "requires x <= 3; requires y <= 4;",
        "2 * x + 3 * y <= 18"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_three_bounds,
        "x: Integer, y: Integer, z: Integer",
        "requires x <= 3; requires y <= 4; requires z <= 5;",
        "2 * x + 3 * y + z <= 23"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_equality_direction,
        "x: Integer, y: Integer",
        "requires x == y + 1; requires y <= 5;",
        "x <= 6"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_antisymmetry,
        "x: Integer, y: Integer",
        "requires x <= y; requires y <= x;",
        "x == y"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_negative_equality_scale,
        "x: Integer, y: Integer",
        "requires x == y + 1;",
        "-2 * x + 2 * y == -2"
    );
    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_equality_sum,
        "x: Integer, y: Integer",
        "requires x == 2; requires y == 3;",
        "x + y == 5"
    );

    composition_case!(
        #[cfg(not(feature = "fast-gate"))]
        #[ignore = "nightly: ordinary expansion and replay"]
        integer_composition_greater_equal_spelling,
        "x: Integer",
        "requires x >= 3;",
        "2 * x >= 6"
    );

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: wide default expansion and replay"]
    fn integer_composition_wide_constant_keeps_integer_context_after_expansion() {
        let source = "theorem composition(z: Integer) { requires 0 <= z; requires z <= 4000; ensures z <= 18446744073709551615 by { close(); } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: two composed branches and replay"]
    fn integer_composition_closes_its_focused_conjunction_branch() {
        let source = "theorem composition(x: Integer) { requires x <= 3; ensures 2 * x <= 6 and 3 * x <= 9 by { all { 2 * x <= 6 => { close() using { x <= 3; }; } 3 * x <= 9 => { close() using { x <= 3; }; } } } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
    fn integer_composition_unrestricted_solve_uses_the_same_ordinary_emitter() {
        let source = "theorem composition(x: Integer, y: Integer) { requires x <= 3; requires y <= 4; ensures 2 * x + 3 * y <= 18 by { close(); } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
    fn integer_composition_preserves_original_alias_and_nonlinear_operand_spellings() {
        for source in [
            "theorem composition(x: Integer, y: Integer) { let z: Integer = x + y; requires z <= 3; ensures 2 * z <= 6 by { close() using { z <= 3; }; } }",
            "theorem composition(x: Integer, y: Integer) { requires x * y <= 3; ensures 2 * (x * y) <= 6 by { close() using { x * y <= 3; }; } }",
        ] {
            let expanded =
                expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
            assert!(!expanded.contains("normalize("), "{expanded}");
            without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 1.4s in the parallel gate"]
    fn an_argument_domain_cites_its_established_bounds_once() {
        // `defined(hi - 1)` asks for `to_integer(hi) - 1 >= -2147483648`;
        // the composition proved it as `-2147483648 <= ...`. The domain
        // cites that fact instead of deriving the bound again. Its other
        // spellings, `defined((hi - 1) as int32)` and `old(...)`, are the
        // same fact here and are not proved again.
        let source = "theorem domain(lo: int32, hi: int32) { requires 0 <= lo; requires lo < hi; requires hi <= 1073741823; ensures 0 <= to_integer(hi - 1) by { close(); } }";
        let expanded = expand_c_claim_source_by_label(source, &[], "domain.ensures_0")
            .unwrap_or_else(|error| panic!("{}", error.report()));
        let (_, domain) = expanded
            .split_once("have defined((hi - 1)) by {")
            .unwrap_or_else(|| panic!("{expanded}"));
        let domain = domain.split("have ").next().unwrap();
        assert!(domain.contains(">= -2147483648 => {"), "{expanded}");
        assert!(
            !expanded.contains("have -2147483648 <= (to_integer(hi) - to_integer(1))"),
            "{expanded}"
        );
        assert_eq!(expanded.matches("have defined(").count(), 1, "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.report()));
    }

    #[test]
    fn integer_composition_does_not_use_an_unlisted_bound() {
        let source = "theorem composition(x: Integer, y: Integer) { requires x <= 3; requires y <= 4; ensures 2 * x + 3 * y <= 18 by { close() using { x <= 3; }; } }";
        assert!(verify_c_sources(source, &[]).is_err());
    }

    #[test]
    fn integer_scaling_requires_an_explicit_certificate_for_checked_replay() {
        let source = "theorem identity(x: Integer, y: Integer) { ensures 3 * (x - y) == x + x + x - 3 * y by { close(); } }";
        verify_c_sources(source, &[]).unwrap();
        crate::surface::without_proof_search_for_claim("identity.ensures_0", || {
            verify_c_sources(source, &[]).map_err(|error| error.report())
        })
        .expect_err("the unexpanded proof needs search");
        for source in [
            "theorem wrong(x: Integer) { ensures 2 * x == x + x + 1 by { close(); } }",
            "theorem ignores_facts(x: Integer) { requires x == 0; ensures 2 * x == 3 * x by { close() using {}; } }",
        ] {
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::tests::*;
    include!("../../../scaling_tests/surface/proof/smart_closures/integer_composition/tests.rs");
}

/// Whether a `defined` candidate's root operation has an operand that owes a
/// domain of its own: an operation or a read rather than a name or literal.
/// Its claim is then that operation's domain alone, over operand values
/// whose own domains the theorem's arguments carry.
pub(super) fn domain_has_compound_operand(domain: &SyntaxProposition) -> bool {
    // A C fragment's operand owes a domain unless it is a value or a local:
    // a static or global object is a memory read.
    fn compound_fragment(operand: &ProgramExpression) -> bool {
        match operand {
            ProgramExpression::Value(_) => false,
            ProgramExpression::Variable(name) => !matches!(
                name,
                crate::kernel::BindingName::Named(_) | crate::kernel::BindingName::Local(_)
            ),
            ProgramExpression::Cast { expression, .. } => compound_fragment(expression),
            _ => true,
        }
    }
    fn compound(operand: &SyntaxTerm) -> bool {
        match operand {
            SyntaxTerm::Binding(_)
            | SyntaxTerm::ProgramBinding(_)
            | SyntaxTerm::IntegerLiteral(_) => false,
            SyntaxTerm::ProgramExpression(fragment) => compound_fragment(fragment),
            _ => true,
        }
    }
    let SyntaxProposition::Defined { expression } = domain else {
        return false;
    };
    let mut root = expression;
    loop {
        match root {
            SyntaxTerm::Old(inner)
            | SyntaxTerm::IntegerContext(inner)
            | SyntaxTerm::At {
                expression: inner, ..
            } => root = inner,
            SyntaxTerm::CUnary { operand, .. } => root = operand,
            _ => break,
        }
    }
    match root {
        SyntaxTerm::Add(left, right)
        | SyntaxTerm::Subtract(left, right)
        | SyntaxTerm::Multiply(left, right) => compound(left) || compound(right),
        SyntaxTerm::ProgramExpression(
            ProgramExpression::Add(left, right)
            | ProgramExpression::Subtract(left, right)
            | ProgramExpression::Multiply(left, right),
        ) => compound_fragment(left) || compound_fragment(right),
        _ => false,
    }
}
