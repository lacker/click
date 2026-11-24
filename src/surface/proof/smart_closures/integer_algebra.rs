//! Bounded algebra discovery whose output contains only named laws and local checks.
//! Products are expanded here, never by a simple checker. Calls and reads are atoms.
use super::*;
use crate::kernel::SharedIntegerTerm;
type Expr = ContractExpression;
type Poly = BTreeMap<Vec<u64>, BigInt>;

fn num(n: impl Into<BigInt>) -> Expr {
    super::super::surface_synthesis::integer_typed_expression(surface_signed_integer_literal(
        &n.into(),
    ))
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(Box::new(a), Box::new(b))
}
fn mul(a: Expr, b: Expr) -> Expr {
    Expr::Multiply(Box::new(a), Box::new(b))
}
fn neg(a: Expr) -> Expr {
    Expr::Negate(Box::new(a))
}
fn eq(a: Expr, b: Expr) -> ClickProposition {
    ClickProposition::Comparison {
        left: super::super::surface_synthesis::integer_typed_expression(a),
        operator: ComparisonOperator::Equal,
        right: b,
    }
}
fn sum(terms: impl IntoIterator<Item = Expr>) -> Expr {
    terms.into_iter().reduce(add).unwrap_or_else(|| num(0))
}
fn product(terms: &[Expr]) -> Expr {
    match terms {
        [] => num(1),
        [one] => one.clone(),
        [head, tail @ ..] => mul(head.clone(), product(tail)),
    }
}
fn have(p: ClickProposition, body: Vec<ProofStep>) -> ProofStep {
    super::super::wide_arithmetic::have(p, body)
}
// Reject non-identities before evaluating Surface arguments or selecting laws.
// In particular, native arithmetic stays an atom while its bridge is proved.
fn symbolic_shape(
    term: &SharedIntegerTerm,
    depth: usize,
    memo: &mut std::collections::HashMap<u64, Poly>,
) -> Option<Poly> {
    use crate::kernel::IntegerTerm;
    if depth >= 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
        return None;
    }
    if let Some(shape) = memo.get(&term.id()) {
        if crate::instrumentation::deadline_exceeded_with_work(shape.len()) {
            return None;
        }
        return Some(shape.clone());
    }
    let mut shape = if let Some(value) = term.as_const() {
        BTreeMap::from([(vec![], value.clone())])
    } else {
        match term.as_ref() {
            IntegerTerm::Add(a, b) | IntegerTerm::Subtract(a, b) => {
                let mut left = symbolic_shape(a, depth + 1, memo)?;
                for (keys, value) in symbolic_shape(b, depth + 1, memo)? {
                    if crate::instrumentation::deadline_exceeded_with_work(
                        value.bits() as usize + 1,
                    ) {
                        return None;
                    }
                    *left.entry(keys).or_default() +=
                        if matches!(term.as_ref(), IntegerTerm::Subtract(..)) {
                            -value
                        } else {
                            value
                        };
                }
                left
            }
            IntegerTerm::Negate(value) => symbolic_shape(value, depth + 1, memo)?
                .into_iter()
                .map(|(keys, value)| (keys, -value))
                .collect(),
            IntegerTerm::Multiply(a, b) => {
                let left = symbolic_shape(a, depth + 1, memo)?;
                let right = symbolic_shape(b, depth + 1, memo)?;
                let mut result = Poly::new();
                for (x, a) in left {
                    for (y, b) in &right {
                        if crate::instrumentation::deadline_exceeded_with_work(
                            (a.bits() as usize + 1).saturating_mul(b.bits() as usize + 1),
                        ) {
                            return None;
                        }
                        let mut keys = x.clone();
                        keys.extend(y);
                        keys.sort_unstable();
                        *result.entry(keys).or_default() += &a * b;
                        if result.len() > 4096 {
                            return None;
                        }
                    }
                }
                result
            }
            _ => BTreeMap::from([(
                vec![SharedIntegerTerm::from(term.value_read().clone()).id()],
                BigInt::one(),
            )]),
        }
    };
    shape.retain(|_, value| !value.is_zero());
    if shape.len() > 4096 {
        return None;
    }
    memo.insert(term.id(), shape.clone());
    Some(shape)
}

#[derive(Clone)]
struct Term {
    keys: Vec<u64>,
    coefficient: BigInt,
}
struct Normal {
    poly: Poly,
    expression: Expr,
}
struct Algebra<'p, 'a> {
    proof: &'p Proof<'a>,
    atoms: BTreeMap<u64, (SharedIntegerTerm, Expr)>,
    steps: Vec<ProofStep>,
    memo: std::collections::HashMap<Expr, Poly>,
    active_aliases: std::collections::HashSet<String>,
    depth: usize,
}
impl<'p, 'a> Algebra<'p, 'a> {
    fn charge(&self, n: usize) -> Result<(), ClickError> {
        if self.steps.len() >= 4096 || crate::instrumentation::deadline_exceeded_with_work(n) {
            Err(self
                .proof
                .step_error("Integer algebra expansion reached its work or 4096-step bound"))
        } else {
            Ok(())
        }
    }
    fn record(
        &mut self,
        a: Expr,
        b: Expr,
        body: Vec<ProofStep>,
    ) -> Result<ClickProposition, ClickError> {
        self.charge(1)?;
        if a == b {
            return Ok(eq(a, b));
        }
        let p = eq(a, b);
        let mut retained = Vec::new();
        for step in body {
            if let ProofStep::Rewrite(identity) = &step
                && let Some((ConditionTerm::IntegerEqual(x, y), true)) = (self
                    .proof
                    .lower_cited_surface_proposition(identity, "algebra rewrite")?)
                .condition_native()
                && x == y
            {
                continue;
            }
            retained.push(step);
        }
        self.steps.push(have(p.clone(), retained));
        Ok(p)
    }
    fn known(&mut self, a: Expr, b: Expr) -> Result<ClickProposition, ClickError> {
        self.record(a, b, vec![ProofStep::Known])
    }
    fn law(
        &mut self,
        name: &str,
        args: Vec<Expr>,
        a: Expr,
        b: Expr,
    ) -> Result<ClickProposition, ClickError> {
        let mut premises = Vec::new();
        for arg in &args {
            super::super::fixed_state_proofs::conversion_conditions::walk_written_expressions(
                arg,
                &mut |e| {
                    // Pure applications form native arguments from their
                    // explicit premises, including arithmetic nested in calls.
                    if matches!(self.proof.context.as_ref(), ProofContext::Pure(_)) {
                        let mut domains = Vec::new();
                        if let Expr::Call { name, arguments } = e
                            && name.rsplit("::").next() == Some("to_integer")
                            && let [value] = arguments.as_slice()
                        {
                            domains.push(value);
                        }
                        if matches!(
                            e,
                            Expr::Add(..)
                                | Expr::Subtract(..)
                                | Expr::Multiply(..)
                                | Expr::Divide(..)
                                | Expr::Remainder(..)
                                | Expr::CUnary { .. }
                                | Expr::ShiftLeft(..)
                                | Expr::ShiftRight(..)
                                | Expr::BitwiseAnd(..)
                                | Expr::ProgramExpression(
                                    ProgramExpression::Add(..)
                                        | ProgramExpression::Subtract(..)
                                        | ProgramExpression::Multiply(..)
                                        | ProgramExpression::Divide(..)
                                        | ProgramExpression::Remainder(..)
                                        | ProgramExpression::ShiftLeft(..)
                                        | ProgramExpression::ShiftRight(..)
                                        | ProgramExpression::BitwiseAnd(..)
                                        | ProgramExpression::Cast { .. }
                                )
                        ) {
                            domains.push(e);
                        }
                        for value in domains {
                            let domain = ClickProposition::Defined {
                                expression: value.clone(),
                            };
                            if let Ok(kernel) = self.proof.lower_cited_surface_proposition(
                                &domain,
                                "Integer algebra argument domain",
                            ) && self
                                .proof
                                .facts()
                                .listed_premise_available(&kernel, &[], false)
                                && !premises.contains(&domain)
                            {
                                premises.push(domain);
                            }
                        }
                    }

                    if let Expr::Call { name, arguments } = e
                        && matches!(
                            name.rsplit("::").next(),
                            Some("truncating_quotient" | "truncating_remainder")
                        )
                        && let [_, divisor] = arguments.as_slice()
                    {
                        let domain = ClickProposition::Comparison {
                            left: divisor.clone(),
                            operator: ComparisonOperator::NotEqual,
                            right: num(0),
                        };
                        if !premises.contains(&domain) {
                            premises.push(domain);
                        }
                    }
                },
            );
        }
        self.record(
            a,
            b,
            vec![
                ProofStep::ApplyPlannedTheorem {
                    application: TheoremApplication {
                        name: format!("click::integer::{name}"),
                        arguments: args,
                    },
                    premises,
                },
                ProofStep::Known,
            ],
        )
    }
    fn term(&self, t: &Term) -> Expr {
        if t.keys.is_empty() {
            return num(t.coefficient.clone());
        }
        let m = product(
            &t.keys
                .iter()
                .map(|k| self.atoms[k].1.clone())
                .collect::<Vec<_>>(),
        );
        if t.coefficient.is_one() {
            m
        } else if t.coefficient == BigInt::from(-1) {
            neg(m)
        } else {
            mul(num(t.coefficient.clone()), m)
        }
    }
    fn terms(p: &Poly) -> Vec<Term> {
        p.iter()
            .map(|(keys, c)| Term {
                keys: keys.clone(),
                coefficient: c.clone(),
            })
            .collect()
    }
    fn expression(&self, p: &Poly) -> Expr {
        sum(Self::terms(p).iter().map(|t| self.term(t)))
    }
    fn factor_items(&self, t: &Term) -> Vec<(Option<u64>, Expr)> {
        // Keep actual coefficients, never introduce synthetic unit factors.
        let coefficient = (!t.coefficient.is_one() || t.keys.is_empty())
            .then(|| (None, num(t.coefficient.clone())));
        coefficient
            .into_iter()
            .chain(t.keys.iter().map(|k| (Some(*k), self.atoms[k].1.clone())))
            .collect()
    }
    fn factors(&self, t: &Term) -> Vec<Expr> {
        self.factor_items(t)
            .into_iter()
            .map(|(_, expression)| expression)
            .collect()
    }
    // Flatten a product of two right-associated chains using one named law per link.
    fn concatenate(&mut self, a: &[Expr], b: &[Expr]) -> Result<Expr, ClickError> {
        self.charge(a.len() + b.len())?;
        let raw = mul(product(a), product(b));
        if a.len() <= 1 {
            return Ok(raw);
        }
        let tail = product(&a[1..]);
        let rhs = mul(a[0].clone(), mul(tail.clone(), product(b)));
        self.law(
            "multiply_associative",
            vec![a[0].clone(), tail, product(b)],
            raw.clone(),
            rhs,
        )?;
        self.concatenate(&a[1..], b)?;
        let target = product(&a.iter().chain(b).cloned().collect::<Vec<_>>());
        self.known(raw, target.clone())?;
        Ok(target)
    }
    fn multiply_terms(&mut self, a: &Term, b: &Term) -> Result<Term, ClickError> {
        self.charge(
            (a.coefficient.bits() as usize + 1).saturating_mul(b.coefficient.bits() as usize + 1),
        )?;
        let raw = mul(self.term(a), self.term(b));
        // Expose signed coefficients without introducing unit factors.
        for t in [a, b] {
            if t.coefficient == BigInt::from(-1) && !t.keys.is_empty() {
                let m = product(
                    &t.keys
                        .iter()
                        .map(|k| self.atoms[k].1.clone())
                        .collect::<Vec<_>>(),
                );
                self.law(
                    "negate_as_product",
                    vec![m.clone()],
                    neg(m.clone()),
                    mul(num(-1), m),
                )?;
            }
            self.known(self.term(t), product(&self.factors(t)))?;
        }
        let fa = self.factors(a);
        let fb = self.factors(b);
        let explicit = mul(product(&fa), product(&fb));
        self.known(raw.clone(), explicit.clone())?;
        let flattened = self.concatenate(&fa, &fb)?;
        let mut fs = self.factor_items(a);
        fs.extend(self.factor_items(b));
        let mut rewrites = Vec::new();
        for end in (1..fs.len()).rev() {
            for i in 0..end {
                self.charge(1)?;
                if fs[i].0 <= fs[i + 1].0 {
                    continue;
                }
                let (x, y) = (fs[i].1.clone(), fs[i + 1].1.clone());
                let p = if i + 2 == fs.len() {
                    self.law(
                        "multiply_commutative",
                        vec![x.clone(), y.clone()],
                        mul(x.clone(), y.clone()),
                        mul(y, x),
                    )?
                } else {
                    let tail = product(
                        &fs[i + 2..]
                            .iter()
                            .map(|(_, e)| e.clone())
                            .collect::<Vec<_>>(),
                    );
                    self.law(
                        "multiply_swap_front",
                        vec![x.clone(), y.clone(), tail.clone()],
                        mul(x.clone(), mul(y.clone(), tail.clone())),
                        mul(y, mul(x, tail)),
                    )?
                };
                rewrites.push(ProofStep::Rewrite(p));
                fs.swap(i, i + 1);
            }
        }
        let sorted = product(&fs.iter().map(|(_, e)| e.clone()).collect::<Vec<_>>());
        rewrites.push(ProofStep::Known);
        self.record(flattened, sorted.clone(), rewrites)?;
        let coefficient = &a.coefficient * &b.coefficient;
        let mut keys = a.keys.clone();
        keys.extend(&b.keys);
        keys.sort_unstable();
        let t = Term { keys, coefficient };
        let mut finish = Vec::new();
        if fs.iter().take_while(|(key, _)| key.is_none()).count() == 2 {
            let numeric = self.known(
                mul(num(a.coefficient.clone()), num(b.coefficient.clone())),
                num(t.coefficient.clone()),
            )?;
            if fs.len() > 2 {
                let tail = product(&fs[2..].iter().map(|(_, e)| e.clone()).collect::<Vec<_>>());
                let association = self.law(
                    "multiply_associative",
                    vec![
                        num(a.coefficient.clone()),
                        num(b.coefficient.clone()),
                        tail.clone(),
                    ],
                    mul(
                        mul(num(a.coefficient.clone()), num(b.coefficient.clone())),
                        tail.clone(),
                    ),
                    sorted.clone(),
                )?;
                finish.push(ProofStep::Rewrite(
                    super::super::fixed_state_proofs::reverse_surface_equality(&association)
                        .expect("an algebra law is an equality"),
                ));
            }
            finish.push(ProofStep::Rewrite(numeric));
        }
        if t.coefficient == BigInt::from(-1) && !t.keys.is_empty() {
            let m = product(
                &t.keys
                    .iter()
                    .map(|k| self.atoms[k].1.clone())
                    .collect::<Vec<_>>(),
            );
            self.law(
                "negate_as_product",
                vec![m.clone()],
                neg(m.clone()),
                mul(num(-1), m),
            )?;
        }
        finish.push(ProofStep::Known);
        self.record(sorted, self.term(&t), finish)?;
        self.known(raw, self.term(&t))?;
        Ok(t)
    }
    fn collect(&mut self, input: Expr, terms: Vec<Term>) -> Result<Normal, ClickError> {
        self.charge(terms.len())?;
        let raw = sum(terms.iter().map(|t| self.term(t)));
        self.known(input.clone(), raw.clone())?;
        let mut groups: BTreeMap<Vec<u64>, Vec<Term>> = BTreeMap::new();
        for t in terms {
            groups.entry(t.keys.clone()).or_default().push(t);
        }
        let grouped = sum(groups
            .values()
            .map(|ts| sum(ts.iter().map(|t| self.term(t)))));
        let order = self.known(raw.clone(), grouped.clone())?;
        let mut substitutions = vec![ProofStep::Rewrite(order)];
        let mut poly = Poly::new();
        for (keys, ts) in groups {
            let group = sum(ts.iter().map(|t| self.term(t)));
            let mut acc = ts[0].clone();
            for next in &ts[1..] {
                let result = Term {
                    keys: keys.clone(),
                    coefficient: &acc.coefficient + &next.coefficient,
                };
                if keys.is_empty() {
                    self.known(add(self.term(&acc), self.term(next)), self.term(&result))?;
                } else {
                    let m = product(
                        &keys
                            .iter()
                            .map(|k| self.atoms[k].1.clone())
                            .collect::<Vec<_>>(),
                    );
                    for t in [&acc, next, &result] {
                        if t.coefficient == BigInt::from(-1) {
                            self.law(
                                "negate_as_product",
                                vec![m.clone()],
                                neg(m.clone()),
                                mul(num(-1), m.clone()),
                            )?;
                        }
                        self.known(self.term(t), mul(num(t.coefficient.clone()), m.clone()))?;
                    }
                    self.law(
                        "multiply_add",
                        vec![
                            num(acc.coefficient.clone()),
                            num(next.coefficient.clone()),
                            m.clone(),
                        ],
                        mul(
                            add(num(acc.coefficient.clone()), num(next.coefficient.clone())),
                            m.clone(),
                        ),
                        add(
                            mul(num(acc.coefficient.clone()), m.clone()),
                            mul(num(next.coefficient.clone()), m),
                        ),
                    )?;
                    self.known(
                        add(num(acc.coefficient.clone()), num(next.coefficient.clone())),
                        num(result.coefficient.clone()),
                    )?;
                    self.known(add(self.term(&acc), self.term(next)), self.term(&result))?;
                }
                acc = result;
            }
            let p = self.known(group.clone(), self.term(&acc))?;
            if group != self.term(&acc) {
                substitutions.push(ProofStep::Rewrite(p));
            }
            if !acc.coefficient.is_zero() {
                poly.insert(keys, acc.coefficient);
            }
        }
        let expression = self.expression(&poly);
        substitutions.push(ProofStep::Known);
        self.record(raw, expression.clone(), substitutions)?;
        self.known(input, expression.clone())?;
        Ok(Normal { poly, expression })
    }
    fn distribute(&mut self, a: Expr, b: Expr) -> Result<Expr, ClickError> {
        self.charge(1)?;
        let raw = mul(a.clone(), b.clone());
        let expanded = if let Expr::Add(x, y) = &a {
            self.law(
                "multiply_add",
                vec![x.as_ref().clone(), y.as_ref().clone(), b.clone()],
                raw.clone(),
                add(
                    mul(x.as_ref().clone(), b.clone()),
                    mul(y.as_ref().clone(), b.clone()),
                ),
            )?;
            add(
                self.distribute(x.as_ref().clone(), b.clone())?,
                self.distribute(y.as_ref().clone(), b)?,
            )
        } else if let Expr::Add(x, y) = &b {
            self.law(
                "multiply_add_left",
                vec![a.clone(), x.as_ref().clone(), y.as_ref().clone()],
                raw.clone(),
                add(
                    mul(a.clone(), x.as_ref().clone()),
                    mul(a.clone(), y.as_ref().clone()),
                ),
            )?;
            add(
                self.distribute(a.clone(), x.as_ref().clone())?,
                self.distribute(a, y.as_ref().clone())?,
            )
        } else {
            return Ok(raw);
        };
        self.known(raw, expanded.clone())?;
        Ok(expanded)
    }
    fn multiply_by_minus_one(&mut self, n: Normal, on_left: bool) -> Result<Normal, ClickError> {
        let value = n.expression.clone();
        let right = mul(value.clone(), num(-1));
        let raw = if on_left {
            mul(num(-1), value.clone())
        } else {
            right.clone()
        };
        if on_left {
            self.law(
                "multiply_commutative",
                vec![num(-1), value.clone()],
                raw.clone(),
                right.clone(),
            )?;
        }
        let unit = mul(value.clone(), num(1));
        self.law(
            "multiply_negate",
            vec![value.clone(), num(1)],
            right,
            neg(unit.clone()),
        )?;
        self.known(unit, value)?;
        let result = self.negative(n)?;
        self.known(raw, result.expression.clone())?;
        Ok(result)
    }
    fn negative(&mut self, n: Normal) -> Result<Normal, ClickError> {
        let input = neg(n.expression.clone());
        let ts = Self::terms(&n.poly);
        // Sums of signed opaque atoms already belong to the additive checker.
        if ts
            .iter()
            .all(|term| term.keys.is_empty() || term.coefficient.abs().is_one())
        {
            let poly = n.poly.into_iter().map(|(keys, c)| (keys, -c)).collect();
            let expression = self.expression(&poly);
            self.known(input, expression.clone())?;
            return Ok(Normal { poly, expression });
        }
        let raw = sum(ts.iter().map(|t| neg(self.term(t))));
        self.known(input.clone(), raw.clone())?;
        let mut result = Poly::new();
        for t in &ts {
            let m = self.term(t);
            self.law(
                "negate_as_product",
                vec![m.clone()],
                neg(m.clone()),
                mul(num(-1), m.clone()),
            )?;
            let negative = self.multiply_terms(
                &Term {
                    keys: vec![],
                    coefficient: BigInt::from(-1),
                },
                t,
            )?;
            self.known(neg(m), self.term(&negative))?;
            result.insert(negative.keys, negative.coefficient);
        }
        let target = self.expression(&result);
        self.known(raw, target.clone())?;
        self.known(input, target.clone())?;
        Ok(Normal {
            poly: result,
            expression: target,
        })
    }
    /// Expose the mathematical operation while keeping each operand
    /// evaluated at the selector of the original expression.
    fn arithmetic_under_point(e: &Expr) -> Option<Expr> {
        let (mut expression, selector) = match e {
            Expr::At {
                selector,
                expression,
            } => (expression.as_ref(), Some(selector)),
            Expr::Old(expression) => (expression.as_ref(), None),
            _ => return None,
        };
        while let Expr::IntegerContext(inner) = expression {
            expression = inner;
        }
        let anchored = |operand: &Expr| {
            let operand = Box::new(operand.clone());
            Box::new(match selector {
                Some(selector) => Expr::At {
                    selector: selector.clone(),
                    expression: operand,
                },
                None => Expr::Old(operand),
            })
        };
        Some(match expression {
            Expr::Add(a, b) => Expr::Add(anchored(a), anchored(b)),
            Expr::Subtract(a, b) => Expr::Subtract(anchored(a), anchored(b)),
            Expr::Multiply(a, b) => Expr::Multiply(anchored(a), anchored(b)),
            Expr::Negate(a) => Expr::Negate(anchored(a)),
            _ => return None,
        })
    }

    fn normalize(&mut self, e: &Expr) -> Result<Normal, ClickError> {
        self.charge(1)?;
        if self.depth >= 256 {
            return Err(self
                .proof
                .step_error("Integer algebra source depth bound reached"));
        }
        self.depth += 1;
        if let Some(poly) = self.memo.get(e).cloned() {
            self.depth -= 1;
            return Ok(Normal {
                expression: self.expression(&poly),
                poly,
            });
        }
        let out = match e {
            Expr::IntegerContext(value) => self.normalize(value)?,
            Expr::At { .. } | Expr::Old(_)
                if let Some(opened) = Self::arithmetic_under_point(e) =>
            {
                let opening = self.known(e.clone(), opened.clone())?;
                let result = self.normalize(&opened)?;
                self.record(
                    e.clone(),
                    result.expression.clone(),
                    vec![ProofStep::Rewrite(opening), ProofStep::Known],
                )?;
                result
            }
            Expr::Let {
                name,
                click_type: Some(ClickType::Integer),
                value,
                body,
            } if matches!(body.as_ref(),Expr::Binding(bound) if bound==name) => {
                self.normalize(value)?
            }
            Expr::Binding(name)
                if !self.active_aliases.contains(name)
                    && self
                        .proof
                        .local_binding(name)
                        .is_some_and(|value| value != e) =>
            {
                let value = self.proof.local_binding(name).unwrap().clone();
                self.active_aliases.insert(name.clone());
                let normalized = self.normalize(&value)?;
                self.active_aliases.remove(name);
                normalized
            }
            Expr::Add(a, b) | Expr::Subtract(a, b) => {
                let a = self.normalize(a)?;
                let mut b = self.normalize(b)?;
                let source = if matches!(e, Expr::Subtract(..)) {
                    Expr::Subtract(
                        Box::new(a.expression.clone()),
                        Box::new(b.expression.clone()),
                    )
                } else {
                    add(a.expression.clone(), b.expression.clone())
                };
                self.known(e.clone(), source.clone())?;
                if matches!(e, Expr::Subtract(..)) {
                    self.known(
                        source.clone(),
                        add(a.expression.clone(), neg(b.expression.clone())),
                    )?;
                    b = self.negative(b)?;
                }
                let input = add(a.expression.clone(), b.expression.clone());
                self.known(source, input.clone())?;
                let terms = Self::terms(&a.poly)
                    .into_iter()
                    .chain(Self::terms(&b.poly))
                    .collect();
                self.collect(input, terms)?
            }
            Expr::Negate(a) => {
                let a = self.normalize(a)?;
                self.known(e.clone(), neg(a.expression.clone()))?;
                self.negative(a)?
            }
            Expr::Multiply(a, b) => {
                let a = self.normalize(a)?;
                let b = self.normalize(b)?;
                let raw = mul(a.expression.clone(), b.expression.clone());
                self.known(e.clone(), raw.clone())?;
                let scalar = |n: &Normal, value: i64| {
                    n.poly.len() == 1 && n.poly.get(&Vec::new()) == Some(&BigInt::from(value))
                };
                if a.poly.is_empty() || b.poly.is_empty() {
                    self.collect(raw, vec![])?
                } else if scalar(&a, 1) {
                    self.known(raw, b.expression.clone())?;
                    b
                } else if scalar(&b, 1) {
                    self.known(raw, a.expression.clone())?;
                    a
                } else if scalar(&a, -1) {
                    self.multiply_by_minus_one(b, true)?
                } else if scalar(&b, -1) {
                    self.multiply_by_minus_one(a, false)?
                } else {
                    self.charge(a.poly.len().saturating_mul(b.poly.len()))?;
                    let expanded = self.distribute(a.expression, b.expression)?;
                    let mut terms = Vec::new();
                    let mut raw_terms = Vec::new();
                    for x in Self::terms(&a.poly) {
                        for y in Self::terms(&b.poly) {
                            raw_terms.push(mul(self.term(&x), self.term(&y)));
                            terms.push(self.multiply_terms(&x, &y)?);
                        }
                    }
                    let pairs = sum(raw_terms);
                    self.known(expanded.clone(), pairs.clone())?;
                    let normalized = sum(terms.iter().map(|t| self.term(t)));
                    self.known(pairs.clone(), normalized.clone())?;
                    let result = self.collect(normalized.clone(), terms)?;
                    self.record(
                        raw.clone(),
                        result.expression.clone(),
                        vec![
                            ProofStep::Rewrite(eq(raw, expanded.clone())),
                            ProofStep::Rewrite(eq(expanded, pairs.clone())),
                            ProofStep::Rewrite(eq(pairs, normalized.clone())),
                            ProofStep::Rewrite(eq(normalized, result.expression.clone())),
                            ProofStep::Known,
                        ],
                    )?;
                    result
                }
            }
            _ => {
                // Use the ordinary argument capture at this proof state. A
                // fresh quantifier would discard the operand's native domains.
                let captured = self.proof.capture_instantiate_integer_argument(e)?;
                // Value-preserving widenings share an arithmetic atom. The
                // ordinary known equation below retains the explicit bridge
                // between this source expression and the chosen atom spelling.
                let term = SharedIntegerTerm::from(captured.value_read().clone());
                let (key, c) = if let Some(c) = term.as_const() {
                    (vec![], c.clone())
                } else {
                    let id = term.id();
                    self.atoms.entry(id).or_insert((term.clone(), e.clone()));
                    (vec![id], BigInt::one())
                };
                let mut poly = Poly::new();
                if !c.is_zero() {
                    poly.insert(key, c);
                }
                Normal {
                    expression: self.expression(&poly),
                    poly,
                }
            }
        };
        self.known(e.clone(), out.expression.clone())?;
        self.memo.insert(e.clone(), out.poly.clone());
        self.depth -= 1;
        Ok(out)
    }
}
/// Look only through the exact arithmetic spine. A let inside an opaque
/// call or read is part of that operand, not algebra for this planner.
fn has_integer_let(expression: &Expr) -> bool {
    let mut pending = vec![expression];
    while let Some(node) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match node {
            Expr::Let {
                click_type: Some(ClickType::Integer),
                ..
            } => return true,
            Expr::IntegerContext(value) | Expr::Negate(value) => pending.push(value),
            Expr::Add(a, b) | Expr::Subtract(a, b) | Expr::Multiply(a, b) => {
                pending.extend([a.as_ref(), b.as_ref()])
            }
            _ => {}
        }
    }
    false
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn try_integer_algebra(
        input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_integer_algebra");
        let Some(original_goal) = input.goal() else {
            return Ok(None);
        };
        let mut goal = original_goal;
        while let Proposition::Not(body) = goal {
            goal = body;
        }
        if !matches!(&goal, condition_source_0 @ Proposition::ConditionIs(_, _) if matches!(condition_source_0.condition_native(), Some((crate::kernel::integer_comparison_condition!(_, _), _))))
        {
            return Ok(None);
        }
        if input
            .goal()
            .is_some_and(crate::kernel::proof::fact_reasoning::computes_leaf)
        {
            return input.driver().apply_step(ProofStep::Known).map(Some);
        }
        // Only inspect the written mathematical arithmetic spine; opaque values
        // keep their meaning and domain. Exact additive leaves need no planner;
        // value-preserving widenings first need their explicit known equations.
        let Some((crate::kernel::integer_comparison_condition!(a, b), _)) = goal.condition_native()
        else {
            return Ok(None);
        };
        let mut pending = vec![a.clone(), b.clone()];
        let mut seen = std::collections::HashSet::new();
        let mut requires_expansion = false;
        while let Some(term) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return Ok(None);
            }
            if !seen.insert(term.id()) {
                continue;
            }
            match term.as_ref() {
                crate::kernel::IntegerTerm::Multiply(..) => {
                    requires_expansion = true;
                    break;
                }
                crate::kernel::IntegerTerm::Add(a, b)
                | crate::kernel::IntegerTerm::Subtract(a, b) => {
                    pending.extend([a.clone(), b.clone()])
                }
                crate::kernel::IntegerTerm::Negate(a) => pending.push(a.clone()),
                _ if term.value_read() != term.as_ref() => {
                    requires_expansion = true;
                    break;
                }
                _ => {}
            }
        }
        if !requires_expansion {
            return Ok(None);
        }
        let mut shapes = std::collections::HashMap::new();
        let Some(left_shape) = symbolic_shape(a, 0, &mut shapes) else {
            return Ok(None);
        };
        let Some(right_shape) = symbolic_shape(b, 0, &mut shapes) else {
            return Ok(None);
        };
        if left_shape
            .iter()
            .filter(|(keys, _)| !keys.is_empty())
            .ne(right_shape.iter().filter(|(keys, _)| !keys.is_empty()))
        {
            return Ok(None);
        }
        let Some(surface) = input
            .surface_goal()
            .and_then(integer_composition::canonical_surface)
        else {
            return Ok(None);
        };
        let ClickProposition::Comparison {
            left,
            operator,
            right,
        } = &surface
        else {
            return Ok(None);
        };
        let open_left = has_integer_let(left);
        let open_right = has_integer_let(right);
        let opened = if *operator == ComparisonOperator::Equal && (open_left || open_right) {
            // Integer lets lower with their lexical bindings resolved.
            // Use the exact raised arithmetic, preserving the original
            // operands on sides that do not need a new spelling.
            let Some(ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            }) = input
                .structural_goal_spelling(original_goal)
                .as_ref()
                .and_then(integer_composition::canonical_surface)
            else {
                return Ok(None);
            };
            Some((left, right))
        } else {
            None
        };
        let (left, right) = match &opened {
            Some((opened_left, opened_right)) => (
                if open_left { opened_left } else { left },
                if open_right { opened_right } else { right },
            ),
            None => (left, right),
        };
        let mut algebra = Algebra {
            proof: input,
            atoms: BTreeMap::new(),
            steps: vec![],
            memo: std::collections::HashMap::new(),
            active_aliases: std::collections::HashSet::new(),
            depth: 0,
        };
        let a = algebra.normalize(left)?;
        let b = algebra.normalize(right)?;
        if a.poly
            .iter()
            .filter(|(k, _)| !k.is_empty())
            .ne(b.poly.iter().filter(|(k, _)| !k.is_empty()))
        {
            return Ok(None);
        }
        let ac = a.poly.get(&Vec::new()).cloned().unwrap_or_default();
        let bc = b.poly.get(&Vec::new()).cloned().unwrap_or_default();
        let true_comparison = match operator {
            ComparisonOperator::Equal => ac == bc,
            ComparisonOperator::NotEqual => ac != bc,
            ComparisonOperator::LessEqual => ac <= bc,
            ComparisonOperator::LessThan => ac < bc,
            ComparisonOperator::GreaterEqual => ac >= bc,
            ComparisonOperator::GreaterThan => ac > bc,
            _ => return Ok(None),
        };
        if !true_comparison {
            return Ok(None);
        }
        for (source, target) in [(left, &a.expression), (right, &b.expression)] {
            let p = eq(source.clone(), target.clone());
            if let Some((ConditionTerm::IntegerEqual(x, y), true)) =
                (input.lower_cited_surface_proposition(&p, "algebra result")?).condition_native()
                && x != y
            {
                algebra.steps.push(ProofStep::Rewrite(p));
            }
        }
        let mut proof = input.clone();
        for step in algebra.steps {
            if proof.focused_discharged() {
                break;
            }
            proof = super::super::without_implicit_solve(|| match step {
                ProofStep::Have {
                    proposition,
                    proof: body,
                } => {
                    let mut scope = proof.driver().open_have(proposition)?;
                    for step in body.steps() {
                        if scope.is_complete() {
                            break;
                        }
                        scope = scope.driver().apply_step(step.clone())?;
                    }
                    scope.join()
                }
                step => proof.driver().apply_step(step),
            })?;
        }
        if !proof.focused_discharged() {
            proof = proof.driver().apply_step(ProofStep::Known)?;
        }
        Ok(Some(proof))
    }
}

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "fast-gate"))]
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: coefficient/polynomial/quotient expansion with search disabled on replay"]
    fn integer_algebra_and_quotient_shifts_expand_without_normalize() {
        let mut failures = Vec::new();
        for source in [
            "theorem bridge(x:Integer,y:Integer) { ensures 3*(x+y)-2*x == x+3*y by close(); }",
            "theorem bridge(x:Integer) { ensures 2*(x+1) == 2*x+2 by close(); }",
            "theorem bridge(x:Integer,y:Integer) { ensures -(-2*x+3*y)+4*y == 2*x+y by close(); }",
            "theorem bridge(a:Integer,b:Integer) { ensures (a+b)*(a-b) == a*a-b*b by close(); }",
            "theorem bridge(a:Integer,b:Integer,c:Integer) { ensures (a*b)*c == c*(b*a) by close(); }",
            "theorem bridge(x:Integer) { ensures 123456789012345678901234567890*x + x == 123456789012345678901234567891*x by close(); }",
            "theorem bridge(x:int32) { ensures 3*to_integer(x)-to_integer(x) == 2*to_integer(x) by close(); }",
            "function f(x:Integer)->Integer {x+1} theorem bridge(x:Integer) { ensures 3*f(x)-f(x) == 2*f(x) by close(); }",
            "theorem bridge(x:Integer,k:Integer) { requires 0<=x; requires 0<=k; ensures truncating_quotient(x+3*k,3)==truncating_quotient(x,3)+k by {close() using {0<=x;0<=k;};} }",
            "theorem bridge(x:Integer,k:Integer) { requires 0<=x; requires 0<=k; ensures k+truncating_quotient(x,3)==truncating_quotient(k*3+x,3) by {close() using {0<=x;0<=k;};} }",
            "theorem bridge(x:Integer,k:Integer) { requires 0<=x; requires 0<=k; ensures k+truncating_quotient(x,3)==truncating_quotient(k*3+x,3) by close(); }",
            "theorem bridge(x:Integer,k:Integer) { requires 0<=x; requires 0<=k; ensures truncating_quotient(x+3*k,3)==truncating_quotient(x,3)+k; }",
        ] {
            let check = (|| -> Result<(), String> {
                verify_c_sources(source, &[]).map_err(|e| e.message().to_owned())?;
                let expanded = expand_c_claim_source_by_label(source, &[], "bridge.ensures_0")
                    .map_err(|e| e.message().to_owned())?;
                if expanded.contains("normalize(") || expanded.contains("solve(") {
                    return Err(expanded);
                }
                without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                    .map_err(|e| format!("{}\n{expanded}", e.message()))?;
                Ok(())
            })();
            if let Err(e) = check {
                failures.push(format!("{source}\n{e}"));
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n\n"));
        // Native bridge leaves retain their independent compatibility paths.
        // This regression checks that algebra analysis keeps their domains.
        let native = "theorem bridge(i:int32,len:int32) { requires 0<=i; requires i<len; ensures to_integer(i)<=to_integer(i+1) by {close() using {0<=i;i<len;};} }";
        verify_c_sources(native, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(native, &[], "bridge.ensures_0").unwrap();
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();

        for source in [
            "theorem bad(x:Integer,y:Integer) { ensures (x+y)*(x-y)==x*x+y*y by close(); }",
            "theorem bad(x:Integer,y:Integer) { requires x==y; ensures 3*x==3*y by {close() using {};} }",
            "theorem bad(x:Integer,k:Integer) {requires 0<=x;requires 0<=k; ensures truncating_quotient(x+3*k,3)==truncating_quotient(x,3)+k by {close() using {0<=k;};} }",
            "theorem bad(x:Integer,k:Integer) {requires 0<=x;requires 0<=k; ensures truncating_quotient(x+3*k,3)==truncating_quotient(x,3)+k by {close() using {0<=x;};} }",
        ] {
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
    }
}
