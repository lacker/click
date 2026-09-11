//! Checked laws for the reserved conversions between structural Nat and Integer.
//!
//! These operations have builtin meanings. In particular their laws never
//! assume a body for the ordinary, user-definable `nat_to_integer` function.
use super::prelude::*;

pub(crate) fn is_conversion_nat_type(ty: &AlgebraicType) -> bool {
    !ty.rigid
        && ty.name == "Nat"
        && ty.arguments.is_empty()
        && ty.has_consistent_root_schema()
        && ty.variants.len() == 2
        && ty
            .variants
            .iter()
            .any(|v| v.name == "Zero" && v.fields.is_empty())
        && ty.variants.iter().any(|v| {
            v.name == "Succ"
                && v.fields
                    == [AlgebraicValueType::Algebraic {
                        name: "Nat".into(),
                        arguments: Vec::new(),
                    }]
        })
}

fn observed_nat(term: &IntegerTerm) -> Option<&AlgebraicTerm> {
    let IntegerTerm::PureFunctionApplication(application) = term else {
        return None;
    };
    let [PureFunctionArgument::Algebraic(value)] = application.arguments() else {
        return None;
    };
    (application.name() == "to_integer"
        && is_conversion_nat_type(&value.algebraic_type)
        && value.is_well_formed())
    .then_some(value)
}

fn converted_integer(term: &AlgebraicTerm) -> Option<&IntegerTerm> {
    let AlgebraicTermNode::PureFunctionApplication { name, arguments } = &term.node else {
        return None;
    };
    let [PureFunctionArgument::Integer(value)] = arguments.as_slice() else {
        return None;
    };
    (name == "to_nat" && is_conversion_nat_type(&term.algebraic_type) && term.is_well_formed())
        .then_some(value)
}

fn observe(term: AlgebraicTerm) -> IntegerTerm {
    IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
        "to_integer".into(),
        vec![PureFunctionArgument::Algebraic(term)],
    ))
}

fn nonnegative(term: IntegerTerm) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::integer_greater_equal(term, IntegerTerm::constant_i64(0)),
        true,
    )
}

/// Check an exact instance of a Nat conversion law. Matching a public lemma
/// name alone never grants a theorem: the kernel checks its complete formula,
/// including the Nat schema, operation names, arities, and nonnegative guard.
pub(crate) fn check_nat_integer_law(name: &str, proposition: &Proposition) -> Option<Theorem> {
    let (guard, goal) = match proposition {
        Proposition::Implies(guard, goal) => (Some(guard.as_ref()), goal.as_ref()),
        goal => (None, goal),
    };
    let valid = match (name, goal) {
        ("nat_integer_zero", Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true)) => {
            guard.is_none() && observed_nat(left).is_some_and(|n| {
                matches!(&n.node, AlgebraicTermNode::Constructor { variant, fields } if variant == "Zero" && fields.is_empty())
            }) && right.as_ref() == &IntegerTerm::constant_i64(0)
        }
        ("nat_integer_succ", Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true)) => {
            let n = observed_nat(left)?;
            let AlgebraicTermNode::Constructor { variant, fields } = &n.node else { return None };
            let [AlgebraicValue::Algebraic(previous)] = fields.as_slice() else { return None };
            guard.is_none() && variant == "Succ" && right.as_ref() == &IntegerTerm::add(observe(previous.clone()), IntegerTerm::constant_i64(1))
        }
        ("nat_integer_nonnegative", Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(left, right), true)) => {
            guard.is_none() && observed_nat(left).is_some() && right.as_ref() == &IntegerTerm::constant_i64(0)
        }
        ("integer_nat_round_trip", Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true)) => {
            let z = converted_integer(observed_nat(left)?)?;
            right.as_ref() == z && guard == Some(&nonnegative(z.clone()))
        }
        ("nat_integer_round_trip", Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right))) => {
            guard.is_none() && observed_nat(converted_integer(left)?) == Some(right)
        }
        ("integer_to_nat_zero", Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right))) => {
            guard.is_none() && converted_integer(left) == Some(&IntegerTerm::constant_i64(0))
                && right.algebraic_type == left.algebraic_type
                && matches!(&right.node, AlgebraicTermNode::Constructor { variant, fields } if variant == "Zero" && fields.is_empty())
        }
        _ => false,
    };
    valid.then(|| Theorem::new(proposition.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_traits::ToPrimitive;
    use std::sync::Arc;

    fn nat_type() -> AlgebraicType {
        let variants: Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "Zero".into(),
                fields: vec![],
            },
            AlgebraicVariantType {
                name: "Succ".into(),
                fields: vec![AlgebraicValueType::Algebraic {
                    name: "Nat".into(),
                    arguments: vec![],
                }],
            },
        ]
        .into();
        AlgebraicType {
            rigid: false,
            name: "Nat".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "Nat".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        }
    }
    fn nat(n: u32) -> AlgebraicTerm {
        AlgebraicTerm {
            algebraic_type: nat_type(),
            node: if n == 0 {
                AlgebraicTermNode::Constructor {
                    variant: "Zero".into(),
                    fields: vec![],
                }
            } else {
                AlgebraicTermNode::Constructor {
                    variant: "Succ".into(),
                    fields: vec![AlgebraicValue::Algebraic(nat(n - 1))],
                }
            },
        }
    }
    fn convert(z: IntegerTerm) -> AlgebraicTerm {
        AlgebraicTerm {
            algebraic_type: nat_type(),
            node: AlgebraicTermNode::PureFunctionApplication {
                name: "to_nat".into(),
                arguments: vec![PureFunctionArgument::Integer(z.into())],
            },
        }
    }
    fn eq(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(a.into(), b.into()), true)
    }
    fn algebraic_eq(a: AlgebraicTerm, b: AlgebraicTerm) -> Proposition {
        Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b))
    }
    // Independent denotation: a Nat is counted structurally; converting a
    // negative Integer chooses Zero only to make the out-of-domain model total.
    fn eval_nat(n: &AlgebraicTerm) -> BigInt {
        match &n.node {
            AlgebraicTermNode::Constructor { variant, fields } if variant == "Zero" => {
                assert!(fields.is_empty());
                0.into()
            }
            AlgebraicTermNode::Constructor { variant, fields } if variant == "Succ" => {
                let [AlgebraicValue::Algebraic(previous)] = fields.as_slice() else {
                    panic!("bad model Nat")
                };
                eval_nat(previous) + 1
            }
            AlgebraicTermNode::PureFunctionApplication { name, arguments } if name == "to_nat" => {
                let [PureFunctionArgument::Integer(z)] = arguments.as_slice() else {
                    panic!("bad model conversion")
                };
                eval_integer(z).max(0.into())
            }
            _ => panic!("unexpected model term"),
        }
    }
    fn eval_integer(z: &IntegerTerm) -> BigInt {
        match z {
            IntegerTerm::Constant(z) => z.clone(),
            IntegerTerm::Add(a, b) => eval_integer(a) + eval_integer(b),
            IntegerTerm::PureFunctionApplication(app) if app.name() == "to_integer" => {
                let [PureFunctionArgument::Algebraic(n)] = app.arguments() else {
                    panic!("bad model observation")
                };
                eval_nat(n)
            }
            _ => panic!("unexpected model Integer"),
        }
    }
    fn holds(p: &Proposition) -> bool {
        match p {
            Proposition::Implies(a, b) => !holds(a) || holds(b),
            Proposition::ConditionIs(ConditionTerm::Constant(value), expected) => value == expected,
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) => {
                eval_integer(a) == eval_integer(b)
            }
            Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(a, b), true) => {
                eval_integer(a) >= eval_integer(b)
            }
            Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) => {
                eval_nat(a) == eval_nat(b)
            }
            _ => panic!("unexpected model proposition"),
        }
    }
    #[test]
    fn nat_integer_laws_have_independent_denotations_and_reject_tampering() {
        for n in 0..8 {
            for (name, proposition) in [
                (
                    "nat_integer_zero",
                    eq(observe(nat(0)), IntegerTerm::constant_i64(0)),
                ),
                (
                    "nat_integer_succ",
                    eq(
                        observe(nat(n + 1)),
                        IntegerTerm::add(observe(nat(n)), IntegerTerm::constant_i64(1)),
                    ),
                ),
                ("nat_integer_nonnegative", nonnegative(observe(nat(n)))),
                (
                    "nat_integer_round_trip",
                    algebraic_eq(convert(observe(nat(n))), nat(n)),
                ),
                (
                    "integer_to_nat_zero",
                    algebraic_eq(convert(IntegerTerm::constant_i64(0)), nat(0)),
                ),
            ] {
                let theorem = check_nat_integer_law(name, &proposition).expect(name);
                assert!(holds(theorem.proposition()), "{name}");
                let false_claim = Proposition::Not(Box::new(proposition));
                assert!(check_nat_integer_law(name, &false_claim).is_none());
            }
        }
        for z in [
            BigInt::from(-1),
            0.into(),
            1.into(),
            BigInt::from(1u8) << 128,
        ] {
            let value = IntegerTerm::Constant(z.clone());
            let conclusion = eq(observe(convert(value.clone())), value.clone());
            let guarded =
                Proposition::Implies(Box::new(nonnegative(value)), Box::new(conclusion.clone()));
            assert!(holds(
                check_nat_integer_law("integer_nat_round_trip", &guarded)
                    .unwrap()
                    .proposition()
            ));
            assert!(check_nat_integer_law("integer_nat_round_trip", &conclusion).is_none());
            assert_eq!(holds(&conclusion), z.to_i64() != Some(-1));
        }
        let ordinary = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
            "nat_to_integer".into(),
            vec![PureFunctionArgument::Algebraic(nat(0))],
        ));
        assert!(
            check_nat_integer_law(
                "nat_integer_zero",
                &eq(ordinary, IntegerTerm::constant_i64(0))
            )
            .is_none()
        );
        let mut malformed = nat(0);
        malformed.algebraic_type.variants = vec![AlgebraicVariantType {
            name: "Zero".into(),
            fields: vec![],
        }]
        .into();
        assert!(
            check_nat_integer_law(
                "nat_integer_zero",
                &eq(observe(malformed), IntegerTerm::constant_i64(0))
            )
            .is_none()
        );
        assert!(
            check_nat_integer_law(
                "nat_integer_succ",
                &eq(observe(nat(1)), IntegerTerm::constant_i64(2))
            )
            .is_none()
        );
    }
}
