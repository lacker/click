// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::*;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::proof::fact_reasoning::{
    ForallInstantiationError, InstanceArgument, check_forall_instantiation, instantiate_universal,
};
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{MachineCastSpelling, MachineTerm};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    uint64_constant,
};

#[test]
fn refuted_disjunction_requires_the_source_and_every_exact_negation() {
    let cases = [71_000, 71_001, 71_002].map(|id| {
        Proposition::condition_is(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(id)),
                MachineTerm::constant(0),
            ),
            true,
        )
    });
    let disjunction = Proposition::Or(
        Box::new(cases[0].clone()),
        Box::new(Proposition::Or(
            Box::new(cases[1].clone()),
            Box::new(cases[2].clone()),
        )),
    );
    let mut context = PureFactContext::new().assume_proposition(disjunction.clone());
    for case in &cases {
        context = context.assume_proposition(Proposition::Not(Box::new(case.clone())));
    }
    // Propagation may add intermediate disjunctions, their remaining arm,
    // and checked falsehood. The certificate must still reject every context
    // missing one of the original supports.
    let goal = Proposition::Equal(
        Term::ProgramValue(int32(0).into()),
        Term::ProgramValue(int32(1).into()),
    );
    let derivation = crate::kernel::search::ProofSearch::derive_proposition(&(context), &goal)
        .expect("all arms are refuted");
    assert!(derivation.check(&context));
    assert!(derivation.context_premises().contains(&disjunction));
    let negations = cases
        .iter()
        .fold(PureFactContext::new(), |negations, case| {
            negations.assume_proposition(Proposition::Not(Box::new(case.clone())))
        });
    assert!(!derivation.check(&negations));
    for skipped in &cases {
        let mut without = PureFactContext::new().assume_proposition(disjunction.clone());
        for case in cases.iter().filter(|case| *case != skipped) {
            without = without.assume_proposition(Proposition::Not(Box::new(case.clone())));
        }
        assert!(!derivation.check(&without));
        assert!(
            crate::kernel::search::ProofSearch::derive_proposition(&(without), &goal).is_none()
        );
    }
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn rigid_parameters_are_typed_values_not_empty_datatypes() {
    let ty = AlgebraicType::parameter("T".into());
    let x = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(0)),
    };
    assert!(x.is_well_formed());
    assert_eq!(ty.value_type(), AlgebraicValueType::Parameter("T".into()));
    assert_ne!(ty, AlgebraicType::parameter("U".into()));
    let mut nominal = ty.clone();
    nominal.rigid = false;
    assert_ne!(ty, nominal);
    assert!(
        !AlgebraicTerm {
            algebraic_type: nominal,
            node: x.node.clone()
        }
        .is_well_formed()
    );
    assert!(
        !AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Fake".into(),
                fields: vec![]
            }
        }
        .is_well_formed()
    );
    assert!(
        !AlgebraicTerm {
            algebraic_type: ty,
            node: AlgebraicTermNode::Match {
                scrutinee: Box::new(x),
                arms: vec![]
            }
        }
        .is_well_formed()
    );
}

fn maybe_int32_type() -> AlgebraicType {
    let arguments = vec![AlgebraicValueType::Program(ProgramType::Int32)];
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "None".to_string(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Some".to_string(),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Maybe".to_string(),
        arguments: arguments.clone(),
    };
    AlgebraicType {
        rigid: false,
        name: "Maybe".to_string(),
        arguments,
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn maybe_constructor(
    algebraic_type: &AlgebraicType,
    variant: &str,
    fields: Vec<ProgramValue>,
) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: variant.to_string(),
            fields: fields.into_iter().map(AlgebraicValue::Program).collect(),
        },
    }
}

#[test]
fn checked_algebraic_constructor_rules_are_sound() {
    let algebraic_type = maybe_int32_type();
    let left = MachineTerm::Variable(Variable(89_000));
    let right = MachineTerm::Variable(Variable(89_001));
    let field_equality =
        Proposition::condition_is(ConditionTerm::equal(left.clone(), right.clone()), true);
    let constructor_equality = Proposition::Equal(
        Term::Algebraic(
            maybe_constructor(
                &algebraic_type,
                "Some",
                vec![ProgramValue::Int32(left.clone())],
            )
            .into(),
        ),
        Term::Algebraic(
            maybe_constructor(
                &algebraic_type,
                "Some",
                vec![ProgramValue::Int32(right.clone())],
            )
            .into(),
        ),
    );

    let injectivity_context =
        PureFactContext::new().assume_proposition(constructor_equality.clone());
    let injectivity = crate::kernel::search::ProofSearch::derive_solve_proposition(
        &(injectivity_context),
        &field_equality,
    )
    .expect("a checked same-constructor equality entails its field equality");
    assert!(injectivity.check(&injectivity_context));

    let congruence_context = PureFactContext::new().assume_proposition(field_equality);
    let congruence = crate::kernel::search::ProofSearch::derive_solve_proposition(
        &(congruence_context),
        &constructor_equality,
    )
    .expect("checked field equalities entail equality of their constructors");
    assert!(congruence.check(&congruence_context));

    let malformed = Proposition::Equal(
        Term::Algebraic(
            maybe_constructor(&algebraic_type, "Some", vec![ProgramValue::UInt32(left)]).into(),
        ),
        Term::Algebraic(
            maybe_constructor(&algebraic_type, "Some", vec![ProgramValue::UInt32(right)]).into(),
        ),
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_solve_proposition(
            &(PureFactContext::new()),
            &malformed
        )
        .is_none(),
        "constructor rules must reject terms that do not match the retained schema"
    );
}

#[test]
fn algebraic_equality_lookup_for_constructor_disequality_is_goal_local() {
    let algebraic_type = maybe_int32_type();
    let model = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(89_020)),
    };
    let source = Proposition::Equal(
        Term::Algebraic(model.clone().into()),
        Term::Algebraic(maybe_constructor(&algebraic_type, "Some", vec![int32(7)]).into()),
    );
    let unrelated = Proposition::Equal(
        Term::Algebraic(
            AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(Variable(89_021)),
            }
            .into(),
        ),
        Term::Algebraic(maybe_constructor(&algebraic_type, "None", vec![]).into()),
    );
    let goal = Proposition::Not(Box::new(Proposition::Equal(
        Term::Algebraic(model.into()),
        Term::Algebraic(maybe_constructor(&algebraic_type, "None", vec![]).into()),
    )));
    let assumptions = PureFactContext::new().assume_proposition(source.clone());
    let derivation =
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(assumptions), &goal)
            .expect("a known constructor proves disequality from every other constructor");
    assert!(derivation.has_typed_atomic_evidence());
    assert!(derivation.check(&assumptions));
    let facts = crate::kernel::proof::PureFactStore::from_ordered(&[source.clone(), unrelated]);
    assert_eq!(facts.algebraic_equalities_mentioning(&goal), vec![source]);
    let unmatched = Proposition::Not(Box::new(Proposition::Equal(
        Term::Algebraic(
            AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(Variable(89_022)),
            }
            .into(),
        ),
        Term::Algebraic(maybe_constructor(&algebraic_type, "None", vec![]).into()),
    )));
    assert!(facts.algebraic_equalities_mentioning(&unmatched).is_empty());
}

#[test]
fn algebraic_equality_lookup_descends_constructor_fields() {
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Empty".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Node".into(),
            fields: vec![AlgebraicValueType::Algebraic {
                name: "Tree".into(),
                arguments: vec![],
            }],
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Tree".into(),
        arguments: vec![],
    };
    let algebraic_type = AlgebraicType {
        rigid: false,
        name: "Tree".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    };
    let value = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(89_030)),
    };
    let middle = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(89_031)),
    };
    let function = AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::PureFunctionApplication {
            name: "shape_left".into(),
            arguments: vec![PureFunctionArgument::Algebraic(value)],
        },
    };
    let source = Proposition::Equal(
        Term::Algebraic(function.clone().into()),
        Term::Algebraic(middle.clone().into()),
    );
    let constructor = |field: AlgebraicTerm| AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Node".into(),
            fields: vec![AlgebraicValue::Algebraic(field)],
        },
    };
    let goal = Proposition::Equal(
        Term::Algebraic(constructor(function).into()),
        Term::Algebraic(constructor(middle).into()),
    );
    let unrelated = Proposition::Equal(
        Term::Algebraic(
            AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(Variable(89_032)),
            }
            .into(),
        ),
        Term::Algebraic(
            AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(Variable(89_033)),
            }
            .into(),
        ),
    );
    let facts = crate::kernel::proof::PureFactStore::from_ordered(&[source.clone(), unrelated]);
    assert_eq!(facts.algebraic_equalities_mentioning(&goal), vec![source]);
}

#[test]
fn algebraic_symbolic_reflexivity_checks_well_formed_terms() {
    let ty = maybe_int32_type();
    let variable = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(89_010)),
    };
    let call = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::PureFunctionApplication {
            name: "opaque".to_string(),
            arguments: vec![PureFunctionArgument::Algebraic(variable.clone())],
        },
    };
    let matched = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Match {
            scrutinee: Box::new(variable),
            arms: vec![
                AlgebraicResultMatchArm {
                    binding_names: Default::default(),
                    variant: "None".to_string(),
                    bindings: vec![],
                    body: call.clone(),
                },
                AlgebraicResultMatchArm {
                    binding_names: Default::default(),
                    variant: "Some".to_string(),
                    bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                        MachineTerm::Variable(Variable(89_011)),
                    ))],
                    body: call.clone(),
                },
            ],
        },
    };
    let equality = |a: &AlgebraicTerm, b: &AlgebraicTerm| {
        Proposition::Equal(
            Term::Algebraic(a.clone().into()),
            Term::Algebraic(b.clone().into()),
        )
    };
    let context = PureFactContext::new();
    for term in [&call, &matched] {
        let goal = equality(term, term);
        assert!(crate::kernel::proof::fact_reasoning::normalizes_context_free(&goal));
        assert!(
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(context), &goal)
                .unwrap()
                .check(&context)
        );
    }
    let mut other = call.clone();
    if let AlgebraicTermNode::PureFunctionApplication { name, .. } = &mut other.node {
        *name = "different".to_string();
    }
    assert!(
        !crate::kernel::proof::fact_reasoning::normalizes_context_free(&equality(&call, &other))
    );
    assert!(
        !crate::kernel::proof::fact_reasoning::normalizes_context_free(&Proposition::Not(
            Box::new(equality(&call, &other))
        ))
    );
    let mut malformed_call = call;
    if let AlgebraicTermNode::PureFunctionApplication { arguments, .. } = &mut malformed_call.node {
        *arguments = vec![PureFunctionArgument::Algebraic(maybe_constructor(
            &ty,
            "Some",
            vec![ProgramValue::UInt32(MachineTerm::constant(0))],
        ))];
    }
    let mut malformed_match = matched;
    if let AlgebraicTermNode::Match { arms, .. } = &mut malformed_match.node {
        arms.pop();
    }
    for term in [malformed_call, malformed_match] {
        let goal = equality(&term, &term);
        assert!(!crate::kernel::proof::fact_reasoning::normalizes_context_free(&goal));
        assert!(
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(context), &goal)
                .is_none()
        );
    }
}

#[test]
fn algebraic_conditions_decide_from_condition_facts_and_keep_checked_polarity() {
    let ty = maybe_int32_type();
    let left = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(89_100)),
    };
    let right = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(89_101)),
    };
    let condition = ConditionTerm::AlgebraicEqual(Box::new(left.clone()), Box::new(right.clone()));
    let equality = Proposition::Equal(Term::Algebraic(left.into()), Term::Algebraic(right.into()));
    assert_eq!(PureFactContext::new().decide(&condition), None);
    for expected in [true, false] {
        let premise = if expected {
            equality.clone()
        } else {
            Proposition::Not(Box::new(equality.clone()))
        };
        let facts = PureFactContext::new().assume_proposition(premise.clone());
        let condition_fact = Proposition::condition_is(condition.clone(), expected);
        // Checked positive model equalities now enter the shared graph, so
        // the raw equality also decides its condition spelling. A raw
        // disequality remains an explicit proposition, not a negative graph
        // edge; its polarity conversion is checked below.
        assert_eq!(facts.decide(&condition), expected.then_some(true));
        assert_eq!(
            PureFactContext::new()
                .assume_proposition(condition_fact.clone())
                .decide(&condition),
            Some(expected)
        );
        assert!(
            crate::kernel::proof::fact_reasoning::condition_polarity_equivalent(
                &premise,
                &condition_fact
            )
        );
        assert!(
            crate::kernel::proof::fact_reasoning::condition_polarity_forms(&condition_fact)
                .contains(&premise)
        );
        assert!(
            !crate::kernel::proof::fact_reasoning::condition_polarity_equivalent(
                &premise,
                &Proposition::condition_is(condition.clone(), !expected)
            )
        );
    }
    let distinct = ConditionTerm::AlgebraicEqual(
        Box::new(maybe_constructor(&ty, "None", vec![])),
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![ProgramValue::Int32(MachineTerm::constant(0))],
        )),
    );
    // Constructors of different variants differ: `decide` reads the
    // distinctness that makes their equation inconsistent (see
    // `distinct_algebraic_constructors_make_the_context_inconsistent`).
    assert_eq!(PureFactContext::new().decide(&distinct), Some(false));
}

#[test]
fn algebraic_condition_substitution_visits_scalar_fields() {
    let ty = maybe_int32_type();
    let variable = Variable(89_102);
    let condition = ConditionTerm::AlgebraicEqual(
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![ProgramValue::Int32(MachineTerm::Variable(variable))],
        )),
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![ProgramValue::Int32(MachineTerm::constant(0))],
        )),
    );
    let mut variables = BTreeSet::new();
    collect_condition_bitvector_variables(&condition, &mut variables);
    assert_eq!(variables, BTreeSet::from([variable]));
    let rewritten =
        substitute_bitvector_variable_in_condition(&condition, variable, &MachineTerm::constant(0));
    // Substitution reaches the scalar field inside the constructor, so the
    // rewritten condition is syntactically the all-constant one. `decide`
    // answers an algebraic equality only from an indexed condition fact, so
    // the rewrite itself is what this test observes.
    let substituted = ConditionTerm::AlgebraicEqual(
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![ProgramValue::Int32(MachineTerm::constant(0))],
        )),
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![ProgramValue::Int32(MachineTerm::constant(0))],
        )),
    );
    assert_eq!(rewritten, substituted);
    let mut rewritten_variables = BTreeSet::new();
    collect_condition_bitvector_variables(&rewritten, &mut rewritten_variables);
    assert!(rewritten_variables.is_empty());
    let value = MachineTerm::If {
        condition: Box::new(condition),
        then_term: Box::new(MachineTerm::constant(1)),
        else_term: Box::new(MachineTerm::constant(0)),
    };
    assert!(!crate::kernel::term_is_shallow_structural_cache_key(&value));
}

#[test]
fn distinct_algebraic_constructors_make_the_context_inconsistent() {
    let algebraic_type = maybe_int32_type();
    let conflict = Proposition::Equal(
        Term::Algebraic(maybe_constructor(&algebraic_type, "None", vec![]).into()),
        Term::Algebraic(maybe_constructor(&algebraic_type, "Some", vec![int32(7)]).into()),
    );
    assert!(
        PureFactContext::new()
            .assume_proposition(conflict)
            .is_inconsistent()
    );
}

#[test]
fn pointer_substitution_replaces_the_block_and_preserves_the_offset() {
    let from = Variable(90_100);
    let replacement = Address {
        base: AddressBase::Symbolic(Variable(90_101)),
        offset: AddressOffset::Constant(8),
    };
    let occurrence = Address {
        base: AddressBase::Symbolic(from),
        offset: AddressOffset::Constant(4),
    };
    let proposition = Proposition::condition_is(
        ConditionTerm::address_equal(occurrence, Address::null()),
        true,
    );

    let substituted =
        crate::kernel::substitute_pointer_variable_in_proposition(&proposition, from, &replacement);
    let Some((ConditionTerm::AddressEqual(left, _), true)) = substituted.condition_native() else {
        panic!("pointer substitution changed the proposition shape");
    };
    assert_eq!(
        **left,
        Address {
            base: AddressBase::Symbolic(Variable(90_101)),
            offset: AddressOffset::Constant(12),
        }
    );
}

#[test]
fn atomic_derivation_evidence_does_not_inline_multi_premise_payloads() {
    let one_step_envelope = 4 * std::mem::size_of::<usize>();
    assert!(
        std::mem::size_of::<AtomicPropositionDerivationEvidence>() <= one_step_envelope,
        "multi-premise evidence must stay behind an indirection so unrelated recursive proof frames do not grow"
    );
}

#[test]
fn int32_le_and_not_lt_equality_derivation_retains_both_exact_premises() {
    let left = MachineTerm::Variable(Variable(90_000));
    let right = MachineTerm::Variable(Variable(90_001));
    let less_equal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let not_less_than = Proposition::condition_is(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        false,
    );
    let goal = Proposition::condition_is(ConditionTerm::equal(left, right), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(less_equal.clone())
        .assume_proposition(not_less_than.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("<= plus not-< should derive int32 equality");
    assert_eq!(
        derivation.int32_le_and_not_lt_implies_equality_premises(),
        Some((&less_equal, &not_less_than))
    );
    assert!(derivation.check(&assumptions));

    let missing = PureFactContext::new().assume_proposition(less_equal);
    assert!(!derivation.check(&missing));
}

#[test]
fn int32_ge_and_not_gt_equality_derivation_retains_both_exact_premises() {
    let left = MachineTerm::Variable(Variable(90_002));
    let right = MachineTerm::Variable(Variable(90_003));
    let greater_equal = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
        true,
    );
    let not_greater_than = Proposition::condition_is(
        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
        false,
    );
    let goal = Proposition::condition_is(ConditionTerm::equal(left, right), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(greater_equal.clone())
        .assume_proposition(not_greater_than.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect(">= plus not-> should derive int32 equality");
    assert_eq!(
        derivation.int32_ge_and_not_gt_implies_equality_premises(),
        Some((&greater_equal, &not_greater_than))
    );
    assert!(derivation.check(&assumptions));

    let missing = PureFactContext::new().assume_proposition(greater_equal);
    assert!(!derivation.check(&missing));
}

#[test]
fn int32_positive_is_nonnegative_derivation_retains_its_exact_premise() {
    let value = MachineTerm::Variable(Variable(90_004));
    let positive = Proposition::condition_is(
        ConditionTerm::signed_less_than(MachineTerm::constant(0), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), value.clone()),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(positive.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("0 < value should derive 0 <= value");
    assert_eq!(
        derivation
            .int32_positive_is_nonnegative_step()
            .map(SignedOrderDerivationStep::premise),
        Some(&positive)
    );
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));

    let reversed_goal = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value, MachineTerm::constant(0)),
        true,
    );
    let reversed = crate::kernel::search::ProofSearch::derive_solve_proposition(
        &(assumptions),
        &reversed_goal,
    )
    .expect("0 < value should derive value >= 0");
    assert_eq!(
        reversed
            .int32_positive_is_nonnegative_step()
            .map(SignedOrderDerivationStep::premise),
        Some(&positive)
    );
    assert!(reversed.check(&assumptions));
}

#[test]
fn int32_negated_strict_successor_bound_retains_its_exact_premise() {
    let value = MachineTerm::Variable(Variable(90_008));
    let premise = Proposition::condition_is(
        ConditionTerm::signed_less_than(value.clone(), MachineTerm::constant(2)),
        false,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), MachineTerm::constant(1)),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("not (value < 2) should derive value >= 1");
    let step = derivation
        .int32_negated_strict_successor_bound_step()
        .expect("the atomic decision should retain its successor-bound premise");
    assert_eq!(step.lower(), &MachineTerm::constant(2));
    assert_eq!(step.upper(), &value);
    assert!(!step.is_strict());
    assert_eq!(step.premise(), &premise);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn int32_successor_le_implies_lt_retains_its_exact_premise() {
    let value = MachineTerm::Variable(Variable(90_009));
    let premise = Proposition::condition_is(
        ConditionTerm::signed_less_equal(MachineTerm::constant(2), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_than(MachineTerm::constant(1), value.clone()),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("2 <= value should derive 1 < value");
    let step = derivation
        .int32_successor_le_implies_lt_step()
        .expect("the atomic decision should retain its adjacent lower bound");
    assert_eq!(step.lower(), &MachineTerm::constant(2));
    assert_eq!(step.upper(), &value);
    assert!(!step.is_strict());
    assert_eq!(step.premise(), &premise);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn int32_constant_lower_bound_weakening_retains_its_exact_premise() {
    let value = MachineTerm::Variable(Variable(90_010));
    let lower = Proposition::condition_is(
        ConditionTerm::signed_less_equal(MachineTerm::constant(3), value.clone()),
        true,
    );
    let reversed = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), MachineTerm::constant(3)),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), value.clone()),
        true,
    );

    for premise in [lower, reversed] {
        let assumptions = PureFactContext::new().assume_proposition(premise.clone());
        let derivation =
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
                .expect("3 <= value should derive 0 <= value");
        let step = derivation
            .int32_constant_lower_bound_weakening_step()
            .expect("the atomic decision should retain its stronger lower bound");
        assert_eq!(step.lower(), &MachineTerm::constant(3));
        assert_eq!(step.upper(), &value);
        assert!(!step.is_strict());
        assert_eq!(step.premise(), &premise);
        assert!(derivation.check(&assumptions));
        assert!(!derivation.check(&PureFactContext::new()));
    }
}

#[test]
fn int32_le_and_neq_strict_derivation_retains_both_exact_premises() {
    let left = MachineTerm::Variable(Variable(90_006));
    let right = MachineTerm::Variable(Variable(90_007));
    let less_equal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let not_equal =
        Proposition::condition_is(ConditionTerm::equal(left.clone(), right.clone()), false);
    let goal = Proposition::condition_is(ConditionTerm::signed_less_than(left, right), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(less_equal.clone())
        .assume_proposition(not_equal.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("<= plus != should derive strict int32 order");
    assert_eq!(
        derivation.int32_le_and_neq_implies_strict_premises(),
        Some((&less_equal, &not_equal))
    );
    assert!(derivation.check(&assumptions));

    let missing = PureFactContext::new().assume_proposition(less_equal);
    assert!(!derivation.check(&missing));
}

#[test]
fn conjunction_builder_has_logarithmic_depth() {
    fn conjunction_depth(proposition: &Proposition) -> usize {
        match proposition {
            Proposition::And(left, right) => {
                1 + conjunction_depth(left).max(conjunction_depth(right))
            }
            _ => 0,
        }
    }

    let propositions = (0..1_024)
        .map(|index| {
            Proposition::condition_is(ConditionTerm::Variable(Variable(300_000 + index)), true)
        })
        .collect();
    let conjunction = proposition_and_all(propositions);

    assert_eq!(conjunction_depth(&conjunction), 10);
}

/// `x < 0` and `x >= 0` are a comparison and its arithmetic negation rather
/// than one condition at both polarities, so `contradicts` recognizes the
/// pair through the fixed list of equivalent spellings. A merely tighter
/// bound such as `x >= 1` is not that negation and stays a non-contradiction.
#[test]
fn contradicts_recognizes_a_comparison_and_its_arithmetic_negation() {
    let value = MachineTerm::Variable(Variable(310_000));
    let negative = Proposition::condition_is(
        ConditionTerm::signed_less_than(value.clone(), MachineTerm::constant(0)),
        true,
    );
    let nonnegative = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), MachineTerm::constant(0)),
        true,
    );
    let at_least_one = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value, MachineTerm::constant(1)),
        true,
    );

    let opposite =
        crate::kernel::proof::PureFactStore::from_ordered(&[negative.clone(), nonnegative]);
    assert!(
        opposite.contradicts(&negative),
        "`x < 0` held beside `x >= 0` contradicts"
    );

    let tighter =
        crate::kernel::proof::PureFactStore::from_ordered(&[negative.clone(), at_least_one]);
    assert!(
        !tighter.contradicts(&negative),
        "`x >= 1` is not the arithmetic negation of `x < 0`"
    );
}

#[test]
fn known_scalar_equality_uses_congruence_without_building_a_fact_index() {
    let a = MachineTerm::Variable(Variable(990_001));
    let b = MachineTerm::Variable(Variable(990_002));
    let c = MachineTerm::Variable(Variable(990_003));
    let left = binary_node!(Int32, Add, Box::new(a.clone()), Box::new(c.clone()));
    let right = binary_node!(Int32, Add, Box::new(b.clone()), Box::new(c));
    let before = PureFactContext::new();
    assert!(!before.int32_values_known_equal(&left, &right));
    let sibling = before.clone();
    let branch = before
        .clone()
        .assume_condition(ConditionTerm::equal(a, b), true);
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(branch.int32_values_known_equal(&left, &right));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!before.int32_values_known_equal(&left, &right));
    assert!(!sibling.int32_values_known_equal(&left, &right));
}

#[test]
fn equality_graph_queries_do_not_build_the_condition_fact_index() {
    let root = MachineTerm::Variable(Variable(210_000));
    let mut assumptions = PureFactContext::new();
    let mut connected = Vec::new();
    for index in 0..32 {
        let term = MachineTerm::Variable(Variable(210_001 + index));
        assumptions =
            assumptions.assume_condition(ConditionTerm::equal(root.clone(), term.clone()), true);
        connected.push(term);
    }
    for index in 0..128 {
        assumptions = assumptions.assume_condition(
            ConditionTerm::signed_less_than(
                MachineTerm::Variable(Variable(220_000 + index)),
                MachineTerm::constant(index as u32),
            ),
            true,
        );
    }
    let _scope = assumptions.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();

    for term in &connected {
        assert!(assumptions.int32_values_known_equal(&root, term));
    }

    assert_eq!(
        PureFactContext::bitvector_equality_index_fact_visits(),
        0,
        "known equality queries must not build or scan the legacy fact index"
    );
}

/// One pure-theorem scenario: a two-step rewrite chain whose conclusion is
/// also an exactly available requirement, so a real kernel proof object can
/// close it by `close()` and issue the completion these constructors consume.
///
/// The chain uses products, which no smart term constructor folds, so the
/// order of the two cited equalities is observable.
struct PureRewriteScenario {
    variables: Vec<Variable>,
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    /// `value == left * amount`, a conjunct of the first requirement.
    value_equality: Proposition,
    /// `left * amount == total`, which rewrites nothing until `value_equality`
    /// has replaced `value`.
    product_equality: Proposition,
}

fn pure_rewrite_scenario() -> PureRewriteScenario {
    let value_var = Variable(90_130);
    let left_var = Variable(90_131);
    let amount_var = Variable(90_132);
    let total_var = Variable(90_133);
    let value = MachineTerm::Variable(value_var);
    let left = MachineTerm::Variable(left_var);
    let amount = MachineTerm::Variable(amount_var);
    let total = MachineTerm::Variable(total_var);
    let product = binary_node!(
        Int32,
        Multiply,
        Box::new(left.clone()),
        Box::new(amount.clone())
    );
    let value_equality =
        Proposition::condition_is(ConditionTerm::equal(value.clone(), product.clone()), true);
    let product_equality = Proposition::condition_is(ConditionTerm::equal(product, total), true);
    let conclusion = Proposition::condition_is(
        ConditionTerm::equal(
            binary_node!(
                Int32,
                Multiply,
                Box::new(value.clone()),
                Box::new(amount.clone())
            ),
            left.clone(),
        ),
        true,
    );
    let requirements = vec![
        Proposition::And(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_add_overflows(left, amount.clone()),
                false,
            )),
            Box::new(value_equality.clone()),
        ),
        Proposition::condition_is(
            ConditionTerm::signed_subtract_overflows(value, amount),
            false,
        ),
        product_equality.clone(),
        conclusion.clone(),
    ];
    PureRewriteScenario {
        variables: vec![value_var, left_var, amount_var, total_var],
        requirements,
        conclusion,
        value_equality,
        product_equality,
    }
}

/// A kernel-issued completion for `conclusion` under exactly `requirements`.
///
/// Nothing here manufactures authority: the record comes from a real proof
/// object that closed its root judgment with an exact `known` step.
fn checked_pure_completion(
    requirements: &[Proposition],
    conclusion: &Proposition,
) -> crate::kernel::proof::CheckedProposition {
    use crate::kernel::proof::{
        OutcomeProofState, ProofBranch, ProofBranchState, ProofObject, ProofObligation,
        PropositionKnownContext, PropositionObligation, PureFactStore,
    };

    let branch = ProofBranch::new(
        ProofObligation::Proposition(PropositionObligation::new(conclusion.clone(), ())),
        ProofBranchState {
            facts: PureFactStore::from_ordered(requirements),
            execution: None,
        },
    );
    let proof: ProofObject<(), ProofObligation<(), std::sync::Arc<OutcomeProofState<()>>>, ()> =
        ProofObject::root((), branch);
    let Ok(closed) = proof.apply_known(PropositionKnownContext::Exact) else {
        panic!("the scenario's conclusion is an exactly available requirement");
    };
    closed
        .completed_proposition()
        .expect("a closed proposition proof issues its completion")
}

#[test]
fn pure_theorem_completion_issues_universally_closed_authority() {
    let scenario = pure_rewrite_scenario();
    let completion = checked_pure_completion(&scenario.requirements, &scenario.conclusion);

    let authority = prove_universally_quantified_pure_implication(
        scenario.requirements.clone(),
        scenario.conclusion.clone(),
        scenario.variables.clone(),
        &completion,
    )
    .expect("a completion of exactly this goal under exactly these requirements is authority");

    let expected = scenario.variables.iter().rev().fold(
        scenario
            .requirements
            .iter()
            .rev()
            .fold(scenario.conclusion.clone(), |body, requirement| {
                Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
            }),
        |body, var| {
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                *var,
                Sort::ProgramInt32,
                body,
            )
        },
    );
    assert_eq!(authority.theorem.proposition(), &expected);
}

#[test]
fn pure_theorem_completion_of_another_conclusion_is_rejected() {
    let scenario = pure_rewrite_scenario();
    let other = scenario.product_equality.clone();
    let completion = checked_pure_completion(&scenario.requirements, &other);

    assert!(
        prove_universally_quantified_pure_implication(
            scenario.requirements.clone(),
            scenario.conclusion.clone(),
            scenario.variables.clone(),
            &completion,
        )
        .is_none()
    );
}

#[test]
fn pure_theorem_completion_with_a_missing_requirement_is_rejected() {
    let scenario = pure_rewrite_scenario();
    let completion = checked_pure_completion(&scenario.requirements, &scenario.conclusion);
    let mut fewer = scenario.requirements.clone();
    fewer.remove(0);

    assert!(
        prove_universally_quantified_pure_implication(
            fewer,
            scenario.conclusion.clone(),
            scenario.variables.clone(),
            &completion,
        )
        .is_none(),
        "an implication may not drop an antecedent the proof assumed"
    );
}

#[test]
fn pure_theorem_rewrite_certificate_issues_closed_authority() {
    let scenario = pure_rewrite_scenario();
    let completion = checked_pure_completion(&scenario.requirements, &scenario.conclusion);

    let authority = prove_universally_quantified_pure_implication_by_int32_rewrites(
        scenario.requirements.clone(),
        scenario.conclusion.clone(),
        scenario.variables.clone(),
        vec![
            scenario.value_equality.clone(),
            scenario.product_equality.clone(),
        ],
        &completion,
    );

    assert!(authority.is_some());
}

#[test]
fn pure_theorem_rewrite_certificate_rejects_unavailable_equality() {
    let scenario = pure_rewrite_scenario();
    let completion = checked_pure_completion(&scenario.requirements, &scenario.conclusion);
    let unavailable = Proposition::condition_is(
        ConditionTerm::equal(
            MachineTerm::Variable(scenario.variables[0]),
            MachineTerm::constant(7),
        ),
        true,
    );

    assert!(
        prove_universally_quantified_pure_implication_by_int32_rewrites(
            scenario.requirements.clone(),
            scenario.conclusion.clone(),
            scenario.variables.clone(),
            vec![unavailable],
            &completion,
        )
        .is_none(),
        "a cited rewrite must be exactly available among the requirements"
    );
}

#[test]
fn pure_theorem_rewrite_certificate_rejects_reordered_rewrites() {
    let scenario = pure_rewrite_scenario();
    let completion = checked_pure_completion(&scenario.requirements, &scenario.conclusion);

    assert!(
        prove_universally_quantified_pure_implication_by_int32_rewrites(
            scenario.requirements.clone(),
            scenario.conclusion.clone(),
            scenario.variables.clone(),
            vec![
                scenario.product_equality.clone(),
                scenario.value_equality.clone(),
            ],
            &completion,
        )
        .is_none(),
        "the second equality rewrites nothing until the first one has been applied"
    );
}

#[test]
fn pure_theorem_rewrite_certificate_rejects_a_completion_of_another_conclusion() {
    let scenario = pure_rewrite_scenario();
    let completion = checked_pure_completion(&scenario.requirements, &scenario.product_equality);

    assert!(
        prove_universally_quantified_pure_implication_by_int32_rewrites(
            scenario.requirements.clone(),
            scenario.conclusion.clone(),
            scenario.variables.clone(),
            vec![scenario.value_equality.clone()],
            &completion,
        )
        .is_none()
    );
}

#[test]
fn int32_le_antisymmetric_axiom_has_the_exact_implications() {
    let left = MachineTerm::Variable(Variable(90_040));
    let right = MachineTerm::Variable(Variable(90_041));
    let theorem = prove_int32_le_antisymmetric(left.clone(), right.clone());
    let le_premise = Proposition::condition_is(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let reverse_le_premise = Proposition::condition_is(
        ConditionTerm::signed_less_equal(right.clone(), left.clone()),
        true,
    );
    let conclusion = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(right),
        },
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(le_premise),
            Box::new(Proposition::Implies(
                Box::new(reverse_le_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn proposition_derivation_honors_active_deadline() {
    let assumptions = PureFactContext::new();
    let proposition = Proposition::condition_is(ConditionTerm::Constant(true), true);
    assert!(
        crate::kernel::search::ProofSearch::derive_proposition(&(assumptions), &proposition)
            .is_some()
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(assumptions), &proposition)
            .is_some()
    );

    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(
            crate::kernel::search::ProofSearch::derive_proposition(&(assumptions), &proposition)
                .is_none()
        );
        assert!(
            crate::kernel::search::ProofSearch::derive_atomic_proposition(
                &(assumptions),
                &proposition
            )
            .is_none()
        );
        assert!(crate::kernel::reasoning::resolution_interrupted());
    });
}

#[test]
fn strict_reverse_order_derives_a_false_comparison() {
    let left = MachineTerm::Variable(Variable(200));
    let right = MachineTerm::Variable(Variable(201));
    let reverse = Proposition::condition_is(
        ConditionTerm::signed_less_than(right.clone(), left.clone()),
        true,
    );
    let target = Proposition::condition_is(ConditionTerm::signed_less_than(left, right), false);
    let assumptions = PureFactContext::new().assume_proposition(reverse.clone());
    let derivation =
        crate::kernel::search::ProofSearch::derive_proposition(&(assumptions), &target)
            .expect("a strict reverse order should prove the comparison false");
    assert_eq!(derivation.context_premises(), vec![reverse]);
    assert!(derivation.check(&assumptions));
    assert!(
        crate::kernel::search::ProofSearch::derive_proposition(
            &(assumptions
                .clone()
                .defer_non_exact_loadability_obligations()),
            &target
        )
        .is_some(),
        "proof construction remains available when symbolic execution defers search"
    );
}

#[test]
fn signed_order_derivation_retains_its_exact_edge_path() {
    let left = MachineTerm::Variable(Variable(202));
    let middle = MachineTerm::Variable(Variable(203));
    let right = MachineTerm::Variable(Variable(204));
    let first = Proposition::condition_is(
        ConditionTerm::signed_less_equal(left.clone(), middle.clone()),
        true,
    );
    let second = Proposition::condition_is(
        ConditionTerm::signed_less_than(middle.clone(), right.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the signed-order chain should derive its conclusion");
    let path = derivation
        .signed_order_path()
        .expect("the atomic decision should retain its selected order path");
    let edge = |step: &OrderDerivationStep| {
        let Proposition::ConditionIs(condition, value) = step.premise() else {
            panic!("order source")
        };
        condition_as_order_fact(condition.native_compat(), *value).unwrap()
    };
    assert_eq!(path.len(), 2);
    assert_eq!(edge(&path[0]).0, left);
    assert_eq!(edge(&path[0]).1, middle);
    assert!(!edge(&path[0]).2);
    assert_eq!(path[0].premise(), &first);
    assert_eq!(edge(&path[1]).0, middle);
    assert_eq!(edge(&path[1]).1, right);
    assert!(edge(&path[1]).2);
    assert_eq!(path[1].premise(), &second);
    assert!(derivation.check(&assumptions));
}

#[test]
fn signed_order_derivation_retains_the_exact_negative_polarity_premise() {
    let left = MachineTerm::Variable(Variable(205));
    let right = MachineTerm::Variable(Variable(206));
    let premise = Proposition::condition_is(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        false,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_than(right.clone(), left.clone()),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the negated non-strict bound should derive reversed strict order");
    let path = derivation
        .signed_order_path()
        .expect("the atomic decision should retain its normalized order edge");
    let edge = |step: &OrderDerivationStep| {
        let Proposition::ConditionIs(condition, value) = step.premise() else {
            panic!("order source")
        };
        condition_as_order_fact(condition.native_compat(), *value).unwrap()
    };
    assert_eq!(path.len(), 1);
    assert_eq!(edge(&path[0]).0, right);
    assert_eq!(edge(&path[0]).1, left);
    assert!(edge(&path[0]).2);
    assert_eq!(path[0].premise(), &premise);
    assert!(derivation.check(&assumptions));
}

#[test]
fn increment_upper_bound_derivation_retains_its_exact_strict_premise() {
    let value = MachineTerm::Variable(Variable(207));
    let upper = MachineTerm::Variable(Variable(208));
    let premise = Proposition::condition_is(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(
            MachineTerm::add(value.clone(), MachineTerm::constant(1)),
            upper.clone(),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the strict bound should derive the increment upper bound");
    let step = derivation
        .int32_increment_upper_bound_step()
        .expect("the atomic decision should retain its named-rule premise");
    assert_eq!(step.lower(), &value);
    assert_eq!(step.upper(), &upper);
    assert!(step.is_strict());
    assert_eq!(step.premise(), &premise);
    assert!(derivation.check(&assumptions));
}

#[test]
fn increment_upper_bound_uses_only_an_exact_direct_strict_edge() {
    let value = MachineTerm::Variable(Variable(207_100));
    let upper = MachineTerm::Variable(Variable(207_101));
    let middle = MachineTerm::Variable(Variable(207_102));
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(
            MachineTerm::add(value.clone(), MachineTerm::constant(1)),
            upper.clone(),
        ),
        true,
    );
    let premises = [
        Proposition::condition_is(
            ConditionTerm::signed_less_than(value.clone(), upper.clone()),
            true,
        ),
        Proposition::condition_is(
            ConditionTerm::signed_less_equal(upper.clone(), value.clone()),
            false,
        ),
        Proposition::condition_is(
            ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
            true,
        ),
        Proposition::condition_is(
            ConditionTerm::signed_greater_equal(value.clone(), upper.clone()),
            false,
        ),
    ];
    for premise in premises {
        let assumptions = PureFactContext::new().assume_proposition(premise.clone());
        let derivation =
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
                .expect("each normalized strict edge derives the increment bound");
        let step = derivation
            .int32_increment_upper_bound_step()
            .expect("the direct rule retains its edge");
        assert_eq!(step.premise(), &premise);
        assert!(derivation.check(&assumptions));
    }

    let indirect = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(value.clone(), middle.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(middle, upper.clone()), true);
    assert!(
        indirect
            .exact_direct_order_step(&value, &upper, true)
            .is_none()
    );
    assert!(
        !indirect
            .selected_for_test()
            .proves_atomic_for_derivation(&goal, true)
    );
}

#[test]
fn increment_constant_upper_bound_retains_its_exact_nonstrict_premise() {
    let value = MachineTerm::Variable(Variable(208_100));
    let direct = Proposition::condition_is(
        ConditionTerm::signed_less_equal(value.clone(), MachineTerm::constant(3)),
        true,
    );
    let reversed = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(MachineTerm::constant(3), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(
            MachineTerm::add(value.clone(), MachineTerm::constant(1)),
            MachineTerm::constant(5),
        ),
        true,
    );

    for premise in [direct, reversed] {
        let assumptions = PureFactContext::new().assume_proposition(premise.clone());
        let derivation =
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
                .expect("value <= 3 should derive value + 1 <= 5");
        let step = derivation
            .int32_increment_constant_upper_bound_step()
            .expect("the atomic decision should retain its non-strict constant bound");
        assert_eq!(step.lower(), &value);
        assert_eq!(step.upper(), &MachineTerm::constant(3));
        assert!(!step.is_strict());
        assert_eq!(step.premise(), &premise);
        assert!(derivation.check(&assumptions));
        assert!(!derivation.check(&PureFactContext::new()));
    }
}

#[test]
fn increment_strictly_increases_derivation_retains_its_exact_strict_premise() {
    let value = MachineTerm::Variable(Variable(209));
    let upper = MachineTerm::Variable(Variable(210));
    let premise = Proposition::condition_is(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_than(
            value.clone(),
            MachineTerm::add(value.clone(), MachineTerm::constant(1)),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the strict upper bound should prove that the increment increases");
    let step = derivation
        .int32_increment_strictly_increases_step()
        .expect("the atomic decision should retain its named-rule premise");
    assert_eq!(step.lower(), &value);
    assert_eq!(step.upper(), &upper);
    assert!(step.is_strict());
    assert_eq!(step.premise(), &premise);
    assert!(derivation.check(&assumptions));
}

#[test]
fn increment_definedness_derivation_retains_its_exact_max_bound() {
    let value = MachineTerm::Variable(Variable(211));
    let int_max = MachineTerm::constant(i32::MAX as u32);
    let premise = Proposition::condition_is(
        ConditionTerm::signed_greater_than(int_max.clone(), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left: Box::new(value.clone()),
            right: Box::new(MachineTerm::constant(1)),
        },
        false,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the strict maximum bound should prove increment definedness");
    let step = derivation
        .int32_increment_below_max_is_defined_premise()
        .expect("the atomic decision should retain its named-rule premise");
    assert_eq!(step, &premise);
    assert!(derivation.check(&assumptions));
}

#[test]
fn one_plus_rules_retain_their_exact_max_bound_and_operand_order() {
    let value = MachineTerm::Variable(Variable(211_050));
    let int_max = MachineTerm::constant(i32::MAX as u32);
    let premise = Proposition::condition_is(
        ConditionTerm::signed_greater_than(int_max.clone(), value.clone()),
        true,
    );
    let one_plus = binary_node!(
        Int32,
        Add,
        Box::new(MachineTerm::constant(1)),
        Box::new(value.clone()),
    );
    let defined_goal = Proposition::condition_is(
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left: Box::new(MachineTerm::constant(1)),
            right: Box::new(value.clone()),
        },
        false,
    );
    let strict_goal = Proposition::condition_is(
        ConditionTerm::signed_less_than(value.clone(), one_plus),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let defined =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &defined_goal)
            .expect("the maximum bound should prove one-plus definedness");
    let defined_step = defined
        .int32_one_plus_below_max_is_defined_premise()
        .expect("definedness must retain the operand-order-specific rule");
    assert_eq!(defined_step, &premise);
    assert!(defined.check(&assumptions));

    let strict =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &strict_goal)
            .expect("the maximum bound should prove one-plus strict increase");
    let strict_step = strict
        .int32_one_plus_strictly_increases_step()
        .expect("strict increase must not select the value-plus-one theorem");
    assert_eq!(strict_step.lower(), &value);
    assert_eq!(strict_step.upper(), &int_max);
    assert!(strict_step.is_strict());
    assert_eq!(strict_step.premise(), &premise);
    assert!(strict.check(&assumptions));
}

#[test]
fn symbolic_add_definedness_retains_both_exact_named_theorem_bounds() {
    let value = MachineTerm::Variable(Variable(211_100));
    let amount = MachineTerm::Variable(Variable(211_101));
    let headroom = binary_node!(
        Int32,
        Subtract,
        Box::new(MachineTerm::constant(i32::MAX as u32)),
        Box::new(amount.clone()),
    );
    let amount_nonnegative = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(amount.clone(), MachineTerm::constant(0)),
        true,
    );
    let within_headroom = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(headroom.clone(), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left: Box::new(value.clone()),
            right: Box::new(amount.clone()),
        },
        false,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(amount_nonnegative.clone())
        .assume_proposition(within_headroom.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the two named-theorem bounds should prove symbolic addition definedness");
    let (nonnegative_step, headroom_step) = derivation
        .int32_nonnegative_add_within_max_premises()
        .expect("the atomic decision should retain both named-theorem premises");
    assert_eq!(nonnegative_step, &amount_nonnegative);
    assert_eq!(headroom_step, &within_headroom);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn symbolic_subtract_definedness_retains_both_exact_named_theorem_bounds() {
    let value = MachineTerm::Variable(Variable(211_110));
    let amount = MachineTerm::Variable(Variable(211_111));
    let amount_nonnegative = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(amount.clone(), MachineTerm::constant(0)),
        true,
    );
    let within_value = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), amount.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Subtract,
            left: Box::new(value.clone()),
            right: Box::new(amount.clone()),
        },
        false,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(amount_nonnegative.clone())
        .assume_proposition(within_value.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the two named-theorem bounds should prove symbolic subtraction definedness");
    let (nonnegative_step, within_value_step) = derivation
        .int32_nonnegative_subtract_within_value_premises()
        .expect("the atomic decision should retain both named-theorem premises");
    assert_eq!(nonnegative_step, &amount_nonnegative);
    assert_eq!(within_value_step, &within_value);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn increment_lower_bound_derivation_retains_both_exact_bounds() {
    let lower = MachineTerm::Variable(Variable(212));
    let value = MachineTerm::Variable(Variable(213));
    let upper = MachineTerm::Variable(Variable(214));
    let lower_premise = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise = Proposition::condition_is(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(
            lower.clone(),
            MachineTerm::add(value.clone(), MachineTerm::constant(1)),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(lower_premise.clone())
        .assume_proposition(upper_premise.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the two exact bounds should prove the increment lower bound");
    let (lower_bound, upper_bound) = derivation
        .int32_increment_lower_bound_steps()
        .expect("the atomic decision should retain both named-rule premises");
    assert_eq!(lower_bound.lower(), &lower);
    assert_eq!(lower_bound.upper(), &value);
    assert!(!lower_bound.is_strict());
    assert_eq!(lower_bound.premise(), &lower_premise);
    assert_eq!(upper_bound.lower(), &value);
    assert_eq!(upper_bound.upper(), &upper);
    assert!(upper_bound.is_strict());
    assert_eq!(upper_bound.premise(), &upper_premise);
    assert!(derivation.check(&assumptions));
}

#[test]
fn remaining_increment_bound_derivations_retain_both_exact_bounds() {
    let lower = MachineTerm::Variable(Variable(218));
    let value = MachineTerm::Variable(Variable(219));
    let upper = MachineTerm::Variable(Variable(220));
    let incremented_value = MachineTerm::add(value.clone(), MachineTerm::constant(1));
    let lower_premise = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise = Proposition::condition_is(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goals = [
        Proposition::condition_is(
            ConditionTerm::signed_greater_equal(incremented_value.clone(), lower.clone()),
            true,
        ),
        Proposition::condition_is(
            ConditionTerm::signed_greater_than(incremented_value, lower.clone()),
            true,
        ),
        Proposition::condition_is(
            ConditionTerm::signed_less_equal(
                MachineTerm::add(lower.clone(), MachineTerm::constant(1)),
                MachineTerm::add(value.clone(), MachineTerm::constant(1)),
            ),
            true,
        ),
    ];
    let assumptions = PureFactContext::new()
        .assume_proposition(lower_premise.clone())
        .assume_proposition(upper_premise.clone());

    for (index, goal) in goals.iter().enumerate() {
        let derivation =
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), goal)
                .expect("the two exact bounds should prove each remaining increment rule");
        let (lower_bound, upper_bound) = match index {
            0 => derivation.int32_increment_greater_equal_lower_bound_steps(),
            1 => derivation.int32_increment_strict_greater_lower_bound_steps(),
            2 => derivation.int32_increment_preserves_order_steps(),
            _ => unreachable!(),
        }
        .expect("the atomic decision should retain the exact named-rule premises");
        assert_eq!(lower_bound.lower(), &lower);
        assert_eq!(lower_bound.upper(), &value);
        assert!(!lower_bound.is_strict());
        assert_eq!(lower_bound.premise(), &lower_premise);
        assert_eq!(upper_bound.lower(), &value);
        assert_eq!(upper_bound.upper(), &upper);
        assert!(upper_bound.is_strict());
        assert_eq!(upper_bound.premise(), &upper_premise);
        assert!(derivation.check(&assumptions));
    }
}

#[test]
fn strict_lower_increment_derivation_retains_both_exact_strict_bounds() {
    let lower = MachineTerm::Variable(Variable(220_100));
    let value = MachineTerm::Variable(Variable(220_101));
    let upper = MachineTerm::Variable(Variable(220_102));
    let lower_premise = Proposition::condition_is(
        ConditionTerm::signed_less_than(lower.clone(), value.clone()),
        true,
    );
    let upper_premise = Proposition::condition_is(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_greater_than(
            MachineTerm::add(value.clone(), MachineTerm::constant(1)),
            lower.clone(),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(lower_premise.clone())
        .assume_proposition(upper_premise.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the two strict bounds should prove the incremented strict lower bound");
    let (lower_bound, upper_bound) = derivation
        .int32_increment_strict_greater_from_strict_lower_steps()
        .expect("the atomic decision should retain both exact strict premises");
    assert_eq!(lower_bound.lower(), &lower);
    assert_eq!(lower_bound.upper(), &value);
    assert!(lower_bound.is_strict());
    assert_eq!(lower_bound.premise(), &lower_premise);
    assert_eq!(upper_bound.lower(), &value);
    assert_eq!(upper_bound.upper(), &upper);
    assert!(upper_bound.is_strict());
    assert_eq!(upper_bound.premise(), &upper_premise);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new().assume_proposition(lower_premise)));
}

#[test]
fn predecessor_derivations_retain_their_exact_named_rule_premises() {
    let value = MachineTerm::Variable(Variable(221));
    let bound = MachineTerm::Variable(Variable(222));
    let zero = MachineTerm::constant(0);
    let predecessor = binary_node!(
        Int32,
        Subtract,
        Box::new(value.clone()),
        Box::new(MachineTerm::constant(1)),
    );
    let positive = Proposition::condition_is(
        ConditionTerm::signed_greater_than(value.clone(), zero.clone()),
        true,
    );
    let nonnegative = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), zero.clone()),
        true,
    );
    let bounded = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(bound.clone(), value.clone()),
        true,
    );

    let positive_assumptions = PureFactContext::new().assume_proposition(positive.clone());
    let nonnegative_goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(zero.clone(), predecessor.clone()),
        true,
    );
    let nonnegative_derivation = crate::kernel::search::ProofSearch::derive_solve_proposition(
        &(positive_assumptions),
        &nonnegative_goal,
    )
    .expect("strict positivity should prove a nonnegative predecessor");
    let nonnegative_step = nonnegative_derivation
        .int32_positive_predecessor_is_nonnegative_step()
        .expect("the decision should retain its exact positivity premise");
    assert_eq!(nonnegative_step.lower(), &zero);
    assert_eq!(nonnegative_step.upper(), &value);
    assert!(nonnegative_step.is_strict());
    assert_eq!(nonnegative_step.premise(), &positive);
    assert!(nonnegative_derivation.check(&positive_assumptions));

    let decrease_goal = Proposition::condition_is(
        ConditionTerm::signed_less_than(predecessor.clone(), value.clone()),
        true,
    );
    let decrease_derivation = crate::kernel::search::ProofSearch::derive_solve_proposition(
        &(positive_assumptions),
        &decrease_goal,
    )
    .expect("strict positivity should prove predecessor decrease");
    let decrease_step = decrease_derivation
        .int32_positive_predecessor_strictly_decreases_step()
        .expect("the decision should retain its exact positivity premise");
    assert_eq!(decrease_step.premise(), &positive);
    assert!(decrease_derivation.check(&positive_assumptions));

    let bounded_assumptions = PureFactContext::new()
        .assume_proposition(nonnegative.clone())
        .assume_proposition(bounded.clone());
    let bounded_goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(predecessor, bound.clone()),
        true,
    );
    let bounded_derivation = crate::kernel::search::ProofSearch::derive_solve_proposition(
        &(bounded_assumptions),
        &bounded_goal,
    )
    .expect("the two exact bounds should prove the predecessor bound");
    let (nonnegative_step, bounded_step) = bounded_derivation
        .int32_nonnegative_predecessor_upper_bound_steps()
        .expect("the decision should retain both exact bound premises");
    assert_eq!(nonnegative_step.lower(), &zero);
    assert_eq!(nonnegative_step.upper(), &value);
    assert!(!nonnegative_step.is_strict());
    assert_eq!(nonnegative_step.premise(), &nonnegative);
    assert_eq!(bounded_step.lower(), &value);
    assert_eq!(bounded_step.upper(), &bound);
    assert!(!bounded_step.is_strict());
    assert_eq!(bounded_step.premise(), &bounded);
    assert!(bounded_derivation.check(&bounded_assumptions));

    let one_le = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), MachineTerm::constant(1)),
        true,
    );
    let one_le_assumptions = PureFactContext::new().assume_proposition(one_le.clone());
    for (goal, nonnegative_result) in [(&nonnegative_goal, true), (&decrease_goal, false)] {
        let derivation = crate::kernel::search::ProofSearch::derive_solve_proposition(
            &(one_le_assumptions),
            goal,
        )
        .expect("one at most the value should prove the predecessor conclusion");
        let step = if nonnegative_result {
            derivation.int32_one_le_predecessor_is_nonnegative_step()
        } else {
            derivation.int32_one_le_predecessor_strictly_decreases_step()
        }
        .expect("the derived predecessor decision should retain its exact one-le source");
        assert_eq!(step.lower(), &MachineTerm::constant(1));
        assert_eq!(step.upper(), &value);
        assert!(!step.is_strict());
        assert_eq!(step.premise(), &one_le);
        assert!(derivation.check(&one_le_assumptions));
    }
}

#[test]
fn predecessor_derivation_retains_equal_one_path_instead_of_a_derived_bound() {
    let value = MachineTerm::Variable(Variable(223));
    let one = MachineTerm::constant(1);
    let predecessor = binary_node!(
        Int32,
        Subtract,
        Box::new(value.clone()),
        Box::new(one.clone())
    );
    let equal_one =
        Proposition::condition_is(ConditionTerm::equal(one.clone(), value.clone()), true);
    let assumptions = PureFactContext::new().assume_proposition(equal_one.clone());

    for (goal, nonnegative_result) in [
        (
            Proposition::condition_is(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), predecessor.clone()),
                true,
            ),
            true,
        ),
        (
            Proposition::condition_is(
                ConditionTerm::signed_less_than(predecessor.clone(), value.clone()),
                true,
            ),
            false,
        ),
    ] {
        let derivation =
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
                .expect("equality to one should prove the predecessor conclusion");
        let path = if nonnegative_result {
            derivation.int32_equal_one_predecessor_is_nonnegative_path()
        } else {
            derivation.int32_equal_one_predecessor_strictly_decreases_path()
        }
        .expect("the predecessor decision should retain its exact equality path");
        assert_eq!(path.len(), 1);
        assert_eq!(path[0].source(), &value);
        assert_eq!(path[0].target(), &one);
        assert_eq!(path[0].premise(), &equal_one);
        assert!(derivation.check(&assumptions));
        assert!(!derivation.check(&PureFactContext::new()));
    }
}

#[test]
fn predecessor_zero_derivation_retains_its_equal_one_path() {
    let value = MachineTerm::Variable(Variable(224));
    let one = MachineTerm::constant(1);
    let zero = MachineTerm::constant(0);
    let predecessor = binary_node!(
        Int32,
        Subtract,
        Box::new(value.clone()),
        Box::new(one.clone())
    );
    let equal_one =
        Proposition::condition_is(ConditionTerm::equal(one.clone(), value.clone()), true);
    let assumptions = PureFactContext::new().assume_proposition(equal_one.clone());

    for goal in [
        Proposition::condition_is(
            ConditionTerm::equal(predecessor.clone(), zero.clone()),
            true,
        ),
        Proposition::condition_is(
            ConditionTerm::equal(zero.clone(), predecessor.clone()),
            true,
        ),
    ] {
        let derivation =
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
                .expect("equality to one should prove that the predecessor is zero");
        let path = derivation
            .int32_equal_one_predecessor_is_zero_path()
            .expect("the predecessor-zero decision should retain its exact equality path");
        assert_eq!(path.len(), 1);
        assert_eq!(path[0].source(), &value);
        assert_eq!(path[0].target(), &one);
        assert_eq!(path[0].premise(), &equal_one);
        assert!(derivation.check(&assumptions));
        assert!(!derivation.check(&PureFactContext::new()));
    }
}

#[test]
fn bitvector_equality_derivation_retains_its_exact_oriented_path() {
    let left = MachineTerm::Variable(Variable(215));
    let middle = MachineTerm::Variable(Variable(216));
    let right = MachineTerm::Variable(Variable(217));
    let first = Proposition::condition_is(ConditionTerm::equal(middle.clone(), left.clone()), true);
    let second =
        Proposition::condition_is(ConditionTerm::equal(middle.clone(), right.clone()), true);
    let goal = Proposition::condition_is(ConditionTerm::equal(left.clone(), right.clone()), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the exact equality chain should derive its conclusion");
    let path = derivation
        .bitvector_equality_path()
        .expect("the atomic decision should retain its selected equality path");
    assert_eq!(path.len(), 2);
    assert_eq!(path[0].source(), &left);
    assert_eq!(path[0].target(), &middle);
    assert_eq!(path[0].premise(), &first);
    assert_eq!(path[1].source(), &middle);
    assert_eq!(path[1].target(), &right);
    assert_eq!(path[1].premise(), &second);
    assert!(derivation.check(&assumptions));
}

#[test]
fn scalar_graph_literal_evaluation_supplies_checkable_solve_equality() {
    let left = MachineTerm::Variable(Variable(218));
    let right = MachineTerm::Variable(Variable(219));
    let one = MachineTerm::constant(1);
    let left_is_one =
        Proposition::condition_is(ConditionTerm::equal(left.clone(), one.clone()), true);
    let right_is_one =
        Proposition::condition_is(ConditionTerm::equal(one.clone(), right.clone()), true);
    let goal = Proposition::condition_is(
        ConditionTerm::equal(
            binary_node!(Int32, Add, Box::new(left.clone()), Box::new(right.clone())),
            MachineTerm::constant(2),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(left_is_one.clone())
        .assume_proposition(right_is_one.clone());

    // Congruence and literal evaluation prove this directly; no contextual
    // representative search or arithmetic normalization is required.
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(assumptions.int32_values_known_equal(
        &binary_node!(Int32, Add, Box::new(left.clone()), Box::new(right.clone())),
        &MachineTerm::constant(2),
    ));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    // Explicit derivation construction may enumerate its premise evidence;
    // that is separate from the Boolean equality query measured above.
    assert_checkable_derivation(&assumptions, &goal);
    assert!(
        crate::kernel::search::ProofSearch::derive_solve_proposition(
            &(PureFactContext::new()),
            &goal
        )
        .is_none()
    );
    assert!(!assumptions.int32_values_known_equal(
        &binary_node!(Int32, Add, Box::new(left), Box::new(right)),
        &MachineTerm::constant(3),
    ));
}

#[test]
fn signed_less_equal_and_inequality_derive_strict_order() {
    let left = MachineTerm::Variable(Variable(9_004));
    let right = MachineTerm::Variable(Variable(9_005));
    let less_equal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let unequal =
        Proposition::condition_is(ConditionTerm::equal(left.clone(), right.clone()), false);
    let strict = Proposition::condition_is(ConditionTerm::signed_less_than(left, right), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(less_equal)
        .assume_proposition(unequal);

    assert_checkable_derivation(&assumptions, &strict);
}

#[test]
fn propagated_implications_need_no_antecedent_search() {
    let target_condition = ConditionTerm::signed_less_than(
        MachineTerm::Variable(Variable(9_001)),
        MachineTerm::Variable(Variable(9_002)),
    );
    let unrelated_condition = ConditionTerm::equal(
        MachineTerm::Variable(Variable(9_003)),
        MachineTerm::Variable(Variable(9_004)),
    );
    let true_fact = Proposition::condition_is(ConditionTerm::Constant(true), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::Implies(
            Box::new(true_fact.clone()),
            Box::new(Proposition::condition_is(unrelated_condition, true)),
        ))
        .assume_proposition(Proposition::Implies(
            Box::new(true_fact),
            Box::new(Proposition::condition_is(target_condition.clone(), true)),
        ));

    PureFactContext::reset_condition_implication_antecedent_checks();
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::condition_is(target_condition, true)
    ));
    assert_eq!(
        PureFactContext::condition_implication_antecedent_checks(),
        0,
        "exact propagation already admitted the target before the query"
    );
}

#[test]
fn merging_required_obligations_preserves_the_certification_frontier() {
    let value = MachineTerm::Variable(Variable(9_010));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::condition_is(
        ConditionTerm::equal(value.clone(), MachineTerm::constant(1)),
        true,
    ));
    let derived = Proposition::condition_is(
        ConditionTerm::signed_less_than(MachineTerm::constant(0), value),
        true,
    );
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &derived
    ));

    let required = ProofObligation::verification_condition(derived.clone());
    let merged = merge_obligations(&[], &[required], &assumptions)
        .expect("required verification conditions should compose");
    assert_eq!(merged.len(), 1);
    assert_eq!(merged[0].proposition(), &derived);
}

#[test]
fn condition_fact_matching_ignores_unrelated_local_memory() {
    let owner = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(100_000)), 4),
    };
    let owner_field = Address {
        base: owner.base.clone(),
        offset: AddressOffset::add(owner.offset.clone(), AddressOffset::Constant(4)),
    };
    let ignored_local = Address {
        base: "local:ignored".into(),
        offset: AddressOffset::Constant(0),
    };
    let empty_memory = SymbolicMemory::new();
    let old_memory = empty_memory.clone().store(
        owner.clone(),
        int32(MachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory(empty_memory))),
            Box::new(owner),
            crate::kernel::LoadKind::Int32,
        )),
    );
    let before_local = SymbolicMemory::new()
        .with_block("call-havoc:8000000", 0)
        .with_block("local:ignored", 4);
    let after_local = before_local
        .clone()
        .with_block("local:ignored", 4)
        .store(ignored_local, int32(MachineTerm::Variable(Variable(1))));
    let old_load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(old_memory))),
        Box::new(owner_field.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let fact = Proposition::condition_is(
        ConditionTerm::equal(
            MachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory(before_local))),
                Box::new(owner_field.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            old_load.clone(),
        ),
        true,
    );
    let target = Proposition::condition_is(
        ConditionTerm::equal(
            MachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory(after_local))),
                Box::new(owner_field),
                crate::kernel::LoadKind::Int32,
            ),
            old_load,
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(fact);

    assert_checkable_derivation(&assumptions, &target);
}

/// Pins what the order check reads: the bounds are stated about loads at one
/// state and asked about the same cells at another that differs by a
/// store to an unrelated local. The order walk used to relate the two loads
/// by resolving them across that store; the difference graph files each
/// state's load as its own term, so the order is left unproved. Execution
/// recording the equality of the two loads when it resolves one would let
/// the graph treat them as one node.
#[test]
fn order_check_does_not_resolve_loads_across_an_unrelated_local_store() {
    let owner = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(100_001)), 4),
    };
    let position = owner.clone();
    let length = owner.offset_by_int32_elements(MachineTerm::constant(1));
    let local = SymbolicMemory::local_pointer("temporary");
    let fact_memory = SymbolicMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block(local.base.clone(), 4)
        .store(local, int32(7));
    let target_memory = SymbolicMemory::new().with_block("call-havoc:0", 0);
    let symbolic_length = MachineTerm::Variable(Variable(100_002));
    let load = |memory: &SymbolicMemory, pointer: &Address| {
        MachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory(memory.clone()))),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(load(&fact_memory, &position), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(load(&fact_memory, &length), symbolic_length.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(1), symbolic_length),
            true,
        );
    let target = ConditionTerm::signed_less_than(
        load(&target_memory, &position),
        load(&target_memory, &length),
    );

    assert!(!assumptions.proves_order_condition_for_memory_resolution(&target, true));
}

#[test]
fn equality_chains_across_observationally_equivalent_memory_loads() {
    let owner = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(100_000)), 4),
    };
    let observed = SymbolicMemory::local_pointer("observed");
    let before_materialized = SymbolicMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block("call-havoc:1", 0)
        .with_block(observed.base.clone(), 4)
        .store(observed, int32(MachineTerm::Variable(Variable(10))));
    let before_sparse = SymbolicMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block("call-havoc:1", 0);
    let after = before_sparse.clone().with_block("call-havoc:3", 0);
    let before_materialized_load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(before_materialized))),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let before_sparse_load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(before_sparse))),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let after_load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(after))),
        Box::new(owner),
        crate::kernel::LoadKind::Int32,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(before_materialized_load, MachineTerm::constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(after_load.clone(), before_sparse_load),
            true,
        );
    let target = Proposition::condition_is(
        ConditionTerm::equal(after_load, MachineTerm::constant(1)),
        true,
    );

    assert_checkable_derivation(&assumptions, &target);
}

#[test]
fn proposition_derivation_proves_implication_from_false_antecedent() {
    let condition =
        ConditionTerm::equal(MachineTerm::Variable(Variable(1)), MachineTerm::constant(0));
    let antecedent = Proposition::condition_is(condition.clone(), false);
    let conclusion = Proposition::Implies(
        Box::new(antecedent),
        Box::new(Proposition::condition_is(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(2)),
                MachineTerm::Variable(Variable(3)),
            ),
            true,
        )),
    );
    let assumptions = PureFactContext::new().assume_condition(condition, true);

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &conclusion)
            .expect("a false antecedent should prove an implication");
    assert!(derivation.check(&assumptions));
}

#[test]
fn builtin_obligation_solver_proves_trivial_props() {
    let assumptions = PureFactContext::new();
    let memory = SymbolicMemory::new().with_block("block", 8);
    let pointer = Address {
        base: "block".into(),
        offset: AddressOffset::Constant(4),
    };

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::Equal(
            Term::Bitvector32(MachineTerm::constant(7).into()),
            Term::Bitvector32(MachineTerm::constant(7).into()),
        )
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::condition_is(ConditionTerm::Constant(true), true)
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: pointer.clone(),
            bytes: (MachineTerm::constant(4)).into(),
            wide: false,
        }
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryCanStore {
            memory,
            pointer,
            byte_width: 4,
        }
    ));
}

/// Range narrowing at element granularity: the one loadability route whose
/// goal span may stay symbolic.
///
/// A segment `p[x..y]` of four-byte elements lowers to the base `p + x * 4`
/// and the span `(y - x) * 4`, so these helpers build exactly the shape the
/// surface produces. Each test then asks `proves`, which is the same decision
/// the implicit check and the explicit `transport ... using` step both reach.
mod loadable_range_narrowing {
    use super::*;

    fn variable(id: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(id))
    }

    fn segment(memory: &SymbolicMemory, start: &MachineTerm, end: &MachineTerm) -> Proposition {
        let origin = Address {
            base: "data".into(),
            offset: AddressOffset::Constant(0),
        };
        Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: origin.offset_by_int32_elements(start.clone()),
            bytes: (MachineTerm::multiply(
                MachineTerm::subtract(end.clone(), start.clone()),
                MachineTerm::constant(4),
            ))
            .into(),
            wide: false,
        }
    }

    fn order(lower: &MachineTerm, upper: &MachineTerm) -> (ConditionTerm, bool) {
        (
            ConditionTerm::signed_less_equal(lower.clone(), upper.clone()),
            true,
        )
    }

    /// The assumed range must also be a valid 32-bit byte span: its element
    /// count pinned to `0..=u32::MAX / 4` for four-byte elements. These are the
    /// two facts a proof states for that; without them the span term is
    /// modular and nothing follows from comparing endpoints.
    fn span_is_valid(a: &MachineTerm, b: &MachineTerm) -> Vec<(ConditionTerm, bool)> {
        let count = MachineTerm::subtract(b.clone(), a.clone());
        let limit = MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4));
        vec![
            order(&MachineTerm::constant(0), &count),
            order(&count, &limit),
        ]
    }

    fn inside(
        a: &MachineTerm,
        b: &MachineTerm,
        c: &MachineTerm,
        d: &MachineTerm,
    ) -> Vec<(ConditionTerm, bool)> {
        let mut orders = vec![order(a, c), order(c, d), order(d, b)];
        orders.extend(span_is_valid(a, b));
        orders
    }

    /// `a`, `b`, `c`, `d`: the assumed range is `p[a..b]` and the goal is
    /// `p[c..d]`.
    fn endpoints() -> [MachineTerm; 4] {
        [
            variable(95_101),
            variable(95_102),
            variable(95_103),
            variable(95_104),
        ]
    }

    fn assume_orders(fact: Proposition, orders: &[(ConditionTerm, bool)]) -> PureFactContext {
        orders.iter().fold(
            PureFactContext::new().assume_proposition(fact),
            |assumptions, (condition, value)| {
                assumptions.assume_condition(condition.clone(), *value)
            },
        )
    }

    #[test]
    fn a_sub_range_the_order_facts_place_inside_is_loadable() {
        let memory = SymbolicMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let assumptions = assume_orders(segment(&memory, &a, &b), &inside(&a, &b, &c, &d));

        assert!(crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &segment(&memory, &c, &d)
        ));
    }

    #[test]
    fn a_sub_range_past_the_assumed_end_is_refused() {
        let memory = SymbolicMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        // `d <= b` is exactly the fact that is missing.
        let assumptions = assume_orders(segment(&memory, &a, &b), &[order(&a, &c), order(&c, &d)]);

        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &segment(&memory, &c, &d)
        ));
    }

    /// A reversed goal range lowers to a negative span. Both ends sit inside
    /// the assumed range, so only the required `c <= d` refuses it.
    #[test]
    fn a_reversed_goal_range_is_refused() {
        let memory = SymbolicMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let mut orders = vec![order(&a, &c), order(&d, &c), order(&c, &b)];
        orders.extend(span_is_valid(&a, &b));
        let assumptions = assume_orders(segment(&memory, &a, &b), &orders);

        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &segment(&memory, &c, &d)
        ));
    }

    /// Loadability is a claim about one memory state. A state in which
    /// the block is no longer there does not inherit the assumed range, so the
    /// order facts alone never carry the conclusion across.
    #[test]
    fn a_different_memory_state_is_refused() {
        let assumed = SymbolicMemory::new().with_block("data", 4096);
        let elsewhere = SymbolicMemory::new().with_block("other", 4096);
        let [a, b, c, d] = endpoints();
        let assumptions = assume_orders(segment(&assumed, &a, &b), &inside(&a, &b, &c, &d));

        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &segment(&elsewhere, &c, &d)
        ));
    }

    /// The wrapped corner, and the reason the rule asks for the assumed range's
    /// byte-count guards at all.
    ///
    /// A span is a `MachineTerm`, so `(b - a) * 4` is modular. At
    /// `b - a == 1 << 30` it is `1 << 32`, which is `0`: the assumed fact then
    /// claims an empty span and is vacuously true, while a sub-range of it is
    /// a real claim. Order facts alone cannot tell those apart, so the rule
    /// refuses unless the count is pinned to `0..=u32::MAX / 4`.
    #[test]
    fn a_wrapped_assumed_span_is_refused() {
        let memory = SymbolicMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        // Everything the narrowing rule reads except the span bound: the goal
        // sits inside the assumed range, and the count is known nonnegative.
        let count = MachineTerm::subtract(b.clone(), a.clone());
        let orders = vec![
            order(&a, &c),
            order(&c, &d),
            order(&d, &b),
            order(&MachineTerm::constant(0), &count),
        ];
        let assumptions = assume_orders(segment(&memory, &a, &b), &orders);

        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &segment(&memory, &c, &d)
        ));
    }

    /// A bound on the count is not enough on its own either. With `a` the least
    /// `int32` and `b` the greatest, `a <= b` holds and `b - a <= limit` holds,
    /// because `b - a` is really `-1`; only the nonnegativity fact excludes it.
    #[test]
    fn a_bounded_but_negative_count_is_refused() {
        let memory = SymbolicMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let count = MachineTerm::subtract(b.clone(), a.clone());
        let limit = MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4));
        let orders = vec![
            order(&a, &c),
            order(&c, &d),
            order(&d, &b),
            order(&count, &limit),
        ];
        let assumptions = assume_orders(segment(&memory, &a, &b), &orders);

        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &segment(&memory, &c, &d)
        ));
    }

    /// A count bounded past the limit is refused even though it is nonnegative:
    /// scaling it by the element width is what leaves the 32-bit span.
    #[test]
    fn a_count_past_the_span_limit_is_refused() {
        let memory = SymbolicMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let count = MachineTerm::subtract(b.clone(), a.clone());
        let past = MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4) + 1);
        let orders = vec![
            order(&a, &c),
            order(&c, &d),
            order(&d, &b),
            order(&MachineTerm::constant(0), &count),
            order(&count, &past),
        ];
        let assumptions = assume_orders(segment(&memory, &a, &b), &orders);

        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &segment(&memory, &c, &d)
        ));
    }

    /// The two spans must be scaled by one element width. A goal counting
    /// one-byte elements is not a sub-range of a four-byte-element fact just
    /// because its endpoints compare, so the rule declines rather than
    /// rescaling a product it would then have to bound against overflow.
    #[test]
    fn a_different_element_width_is_refused() {
        let memory = SymbolicMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let origin = Address {
            base: "data".into(),
            offset: AddressOffset::Constant(0),
        };
        let byte_goal = Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: origin.offset_by_elements(c.clone(), 1),
            bytes: (MachineTerm::multiply(
                MachineTerm::subtract(d.clone(), c.clone()),
                MachineTerm::constant(1),
            ))
            .into(),
            wide: false,
        };
        let assumptions = assume_orders(segment(&memory, &a, &b), &inside(&a, &b, &c, &d));

        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &byte_goal
        ));
    }
}

#[test]
fn empty_memory_range_is_vacuously_loadable() {
    let proposition = Proposition::MemoryLoadable {
        memory: SymbolicMemory::new(),
        base: Address {
            base: "not-live".into(),
            offset: AddressOffset::Variable(Variable(1)),
        },
        bytes: (MachineTerm::constant(0)).into(),
        wide: false,
    };

    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &proposition
    ));
}

#[test]
fn deferred_obligations_keep_contextual_memory_proofs_explicit() {
    let memory = SymbolicMemory::new();
    let base = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let range = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: (MachineTerm::constant(8)).into(),
        wide: false,
    };
    let element = Proposition::MemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(MachineTerm::constant(1)),
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };
    let assumptions = PureFactContext::new().assume_proposition(range);

    let mut ordinary = Vec::new();
    assert!(add_proof_obligation(&mut ordinary, &assumptions, element.clone()).is_some());
    assert!(
        ordinary.is_empty(),
        "ordinary execution may solve the range"
    );

    let mut deferred = Vec::new();
    let deferred_assumptions = assumptions.defer_non_exact_loadability_obligations();
    assert!(add_proof_obligation(&mut deferred, &deferred_assumptions, element.clone()).is_some());
    assert_eq!(deferred.len(), 1);
    assert_eq!(deferred[0].proposition(), &element);
}

/// Lowering emits a structured obligation instead of discharging it.
///
/// The exact route and the retained atomic memory/resource checkers are the
/// only suppression routes left in `add_proof_obligation`. A proposition with
/// logical structure that the general prover could derive from the ambient
/// context is now an explicit obligation for a Surface tactic to close.
#[test]
fn structured_obligations_are_emitted_rather_than_derived() {
    let guard = ConditionTerm::signed_less_than(
        MachineTerm::Variable(Variable(96_001)),
        MachineTerm::constant(10),
    );
    let conclusion = ConditionTerm::signed_less_than(
        MachineTerm::Variable(Variable(96_002)),
        MachineTerm::constant(10),
    );
    let assumptions = PureFactContext::new().assume_condition(conclusion.clone(), true);
    let structured = Proposition::Implies(
        Box::new(Proposition::condition_is(guard, true)),
        Box::new(Proposition::condition_is(conclusion.clone(), true)),
    );
    assert!(
        crate::kernel::search::ProofSearch::proves(&(assumptions), &structured),
        "the general prover derives this implication from its consequent"
    );

    let mut obligations = Vec::new();
    assert!(add_proof_obligation(&mut obligations, &assumptions, structured.clone()).is_some());
    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].proposition(), &structured);

    // The exactly assumed conjunct is still suppressed: exact availability is
    // a lookup, not a proof search.
    let mut exact = Vec::new();
    assert!(
        add_proof_obligation(
            &mut exact,
            &assumptions,
            Proposition::condition_is(conclusion, true)
        )
        .is_some()
    );
    assert!(exact.is_empty());
}

#[test]
fn memory_derivation_records_the_selected_range_candidate() {
    let memory = SymbolicMemory::new();
    let data = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let unrelated = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: Address {
            base: "unrelated".into(),
            offset: AddressOffset::Constant(0),
        },
        bytes: (MachineTerm::constant(64)).into(),
        wide: false,
    };
    let selected = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: (MachineTerm::constant(8)).into(),
        wide: false,
    };
    let target = Proposition::MemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(MachineTerm::constant(1)),
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(unrelated)
        .assume_proposition(selected.clone());
    let derivation =
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(assumptions), &target)
            .expect("the selected range should establish the element access");

    assert!(derivation.check(&assumptions));
    assert_eq!(derivation.context_premises(), vec![selected]);
}

#[test]
fn loadable_symbolic_subrange_proves_an_indexed_cell() {
    let memory = SymbolicMemory::new();
    let data = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let split = MachineTerm::Variable(Variable(87));
    let index = MachineTerm::Variable(Variable(88));
    let len = MachineTerm::Variable(Variable(89));
    let range = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: data.offset_by_int32_elements(split.clone()),
        bytes: (MachineTerm::multiply(
            MachineTerm::subtract(len.clone(), split.clone()),
            MachineTerm::constant(4),
        ))
        .into(),
        wide: false,
    };
    let target = Proposition::MemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(index.clone()),
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };
    // Reading `[split..len]` as its element count needs that count to be a
    // valid byte span once scaled by four; a stated range carries this.
    let count = MachineTerm::subtract(len.clone(), split.clone());
    let assumptions = PureFactContext::new()
        .assume_proposition(range)
        .assume_condition(
            ConditionTerm::signed_less_equal(split.clone(), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), len.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), count.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(
                count,
                MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4)),
            ),
            true,
        );

    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(assumptions), &target)
            .is_some(),
        "split <= index < len should select a cell from [split..len]"
    );
}

#[test]
fn adjacent_loadable_regions_certify_their_concatenation() {
    let memory = SymbolicMemory::new();
    let data = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let prefix = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: (MachineTerm::constant(8)).into(),
        wide: false,
    };
    let next_cell = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: data.offset_by_int32_elements(MachineTerm::constant(2)),
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };
    let goal = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: (MachineTerm::constant(12)).into(),
        wide: false,
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(prefix.clone())
        .assume_proposition(next_cell.clone());
    let derivation =
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(assumptions), &goal)
            .expect("an initialized next cell should extend the viewable prefix");
    assert!(derivation.check(&assumptions));
    let premises = derivation.context_premises();
    assert_eq!(premises.len(), 2);
    assert!(premises.contains(&prefix));
    assert!(premises.contains(&next_cell));

    let stored_memory = SymbolicMemory::new().store(
        data.offset_by_int32_elements(MachineTerm::constant(2)),
        ProgramValue::Int32(MachineTerm::constant(9)),
    );
    let stored_goal = Proposition::MemoryLoadable {
        memory: stored_memory,
        base: data.clone(),
        bytes: (MachineTerm::constant(12)).into(),
        wide: false,
    };
    let stored_assumptions = PureFactContext::new().assume_proposition(prefix.clone());
    let stored_derivation = crate::kernel::search::ProofSearch::derive_atomic_proposition(
        &(stored_assumptions),
        &stored_goal,
    )
    .expect("a materialized next cell should extend the viewable prefix");
    assert!(stored_derivation.check(&stored_assumptions));
    assert_eq!(stored_derivation.context_premises(), vec![prefix]);

    let gap = Proposition::MemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(MachineTerm::constant(4)),
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(goal.clone())
        .assume_proposition(gap);
    let too_wide = Proposition::MemoryLoadable {
        memory: SymbolicMemory::new(),
        base: data,
        bytes: (MachineTerm::constant(16)).into(),
        wide: false,
    };
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &too_wide
    ));
}

#[test]
fn field_derived_capacity_range_covers_a_shorter_live_prefix() {
    let entry_memory = SymbolicMemory::new();
    let owner = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(100_000)), 4),
    };
    let field = |byte_offset| Address {
        base: owner.base.clone(),
        offset: AddressOffset::Add(
            Box::new(owner.offset.clone()),
            Box::new(AddressOffset::Constant(byte_offset)),
        ),
    };
    let len = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory_ref(&entry_memory))),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let after_len = entry_memory
        .clone()
        .store(owner.clone(), ProgramValue::Int32(len.clone()));
    let cap = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory_ref(&after_len))),
        Box::new(field(4)),
        crate::kernel::LoadKind::Int32,
    );
    let after_cap = after_len
        .clone()
        .store(field(4), ProgramValue::Int32(cap.clone()));
    let range_data_offset = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory_ref(&after_cap))),
        Box::new(field(8)),
        crate::kernel::LoadKind::Int32,
    );
    let range_data = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scaled_int32_node(range_data_offset, 4),
    };
    let entry_data_offset = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory_ref(&entry_memory))),
        Box::new(field(8)),
        crate::kernel::LoadKind::Int32,
    );
    let entry_data = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scaled_int32_node(entry_data_offset, 4),
    };
    let index = MachineTerm::Variable(Variable(2_000_000));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::MemoryLoadable {
            memory: after_cap,
            base: range_data,
            bytes: (MachineTerm::multiply(cap.clone(), MachineTerm::constant(4))).into(),
            wide: false,
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), len.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(len, cap.clone()), true)
        // The capacity range is read as `cap` elements, so `cap` has to be a
        // count whose four-byte span does not wrap; the clause that states
        // the range carries this.
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), cap.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(
                cap,
                MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4)),
            ),
            true,
        );
    let target = Proposition::MemoryLoadable {
        memory: entry_memory,
        base: entry_data.offset_by_int32_elements(index),
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };

    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(assumptions), &target)
            .is_some(),
        "a field-derived capacity range must cover an entry-written live-prefix cell"
    );
}

#[test]
fn quantified_int32_fact_does_not_certify_an_instantiated_load() {
    let memory = SymbolicMemory::new();
    let data = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let fact_index = Variable(2_100_000);
    let target_index = Variable(2_100_001);
    let length = MachineTerm::Variable(Variable(2_100_002));
    let indexed_fact_pointer = data.offset_by_int32_elements(MachineTerm::Variable(fact_index));
    let loaded_value = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
        Box::new(indexed_fact_pointer),
        crate::kernel::LoadKind::Int32,
    );
    let guarded_fact = forall_int32(
        fact_index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_equal(
                        MachineTerm::constant(0),
                        MachineTerm::Variable(fact_index),
                    ),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(fact_index),
                        length.clone(),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(loaded_value, MachineTerm::constant(7)),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(guarded_fact)
        .assume_condition(
            ConditionTerm::signed_less_equal(
                MachineTerm::constant(0),
                MachineTerm::Variable(target_index),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(MachineTerm::Variable(target_index), length),
            true,
        );
    let target = Proposition::MemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(MachineTerm::Variable(target_index)),
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };

    assert!(
        !crate::kernel::search::ProofSearch::proves(&(assumptions), &target),
        "a logical value fact cannot grant viewability"
    );
    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &target
        ));
    });
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new().assume_proposition(forall_int32(
            fact_index,
            Proposition::condition_is(ConditionTerm::Constant(true), true),
        ))),
        &target
    ));
}

#[test]
fn quantified_loadability_fact_certifies_an_instantiated_load() {
    let memory = SymbolicMemory::new().with_block("data", 16);
    let data = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let fact_index = Variable(2_100_020);
    let target_index = Variable(2_100_021);
    let length = MachineTerm::Variable(Variable(2_100_022));
    let guard_for = |index| {
        Proposition::And(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_equal(
                    MachineTerm::constant(0),
                    MachineTerm::Variable(index),
                ),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(MachineTerm::Variable(index), length.clone()),
                true,
            )),
        )
    };
    let guarded_fact = forall_int32(
        fact_index,
        Proposition::Implies(
            Box::new(guard_for(fact_index)),
            Box::new(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: data.offset_by_int32_elements(MachineTerm::Variable(fact_index)),
                bytes: (MachineTerm::constant(4)).into(),
                wide: false,
            }),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(guarded_fact)
        .assume_proposition(guard_for(target_index));

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory,
            base: data.offset_by_int32_elements(MachineTerm::Variable(target_index)),
            bytes: (MachineTerm::constant(4)).into(),
            wide: false,
        }
    ));
}

#[test]
fn quantified_signed_condition_fact_certifies_a_symbolic_index() {
    let fact_index = Variable(2_110_000);
    let target_index = Variable(2_110_001);
    let length = MachineTerm::Variable(Variable(2_110_002));
    let guard = |index: Variable| {
        Proposition::And(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_equal(
                    MachineTerm::constant(0),
                    MachineTerm::Variable(index),
                ),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(MachineTerm::Variable(index), length.clone()),
                true,
            )),
        )
    };
    let fact = forall_int32(
        fact_index,
        Proposition::Implies(
            Box::new(guard(fact_index)),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_equal(
                    MachineTerm::Variable(fact_index),
                    MachineTerm::constant(1),
                ),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(fact.clone())
        .assume_proposition(guard(target_index));
    let target = Proposition::condition_is(
        ConditionTerm::signed_less_equal(
            MachineTerm::Variable(target_index),
            MachineTerm::constant(1),
        ),
        true,
    );

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &target)
            .expect("a universal with symbolic bounds should specialize at the target index");
    let (selected, argument, guards) = derivation
        .forall_int32_instantiation()
        .expect("the specialization should retain its universal evidence");
    assert_eq!(selected, &fact);
    assert_eq!(argument, &MachineTerm::Variable(target_index));
    assert_eq!(guards.len(), 2);
    assert!(derivation.check(&assumptions));
}

#[test]
fn quantified_atomic_derivation_retains_its_specialization_and_guards() {
    let memory = SymbolicMemory::new();
    let data = Address {
        base: "typed-quantified-data".into(),
        offset: AddressOffset::Constant(0),
    };
    let index = Variable(2_100_100);
    let exit = MachineTerm::Variable(Variable(2_100_101));
    let indexed_load = |value| {
        MachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
            Box::new(data.offset_by_int32_elements(value)),
            crate::kernel::LoadKind::Int32,
        )
    };
    let quantified = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_equal(
                        MachineTerm::constant(0),
                        MachineTerm::Variable(index),
                    ),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_than(MachineTerm::Variable(index), exit.clone()),
                    true,
                )),
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(
                    indexed_load(MachineTerm::Variable(index)),
                    MachineTerm::Variable(index),
                ),
                true,
            )),
        ),
    );
    // The instantiation guard is stated exactly. Package 15 narrowed the
    // `ForallInt32Instantiation` rule to guards that are builtin solvable or
    // exactly available, because the evidence must name the premises it
    // consumed and the frozen condition checker does not report its own. The
    // `a_quantified_instantiation_guard_needing_a_derivation_is_refused` test
    // below pins that narrowing.
    let exit_guard = Proposition::condition_is(
        ConditionTerm::signed_less_than(MachineTerm::constant(2), exit.clone()),
        true,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::equal(
            indexed_load(MachineTerm::constant(2)),
            MachineTerm::constant(2),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(quantified.clone())
        .assume_proposition(exit_guard.clone());

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("the selected universal instance should prove the concrete cell");
    let (selected, argument, guards) = derivation
        .forall_int32_instantiation()
        .expect("the atomic decision should retain its specialization");
    assert_eq!(selected, &quantified);
    assert_eq!(argument, &MachineTerm::constant(2));
    assert_eq!(guards, std::slice::from_ref(&exit_guard));
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new().assume_proposition(quantified)));
    assert!(!derivation.check(&PureFactContext::new().assume_proposition(exit_guard)));
}

/// Package 15's narrowing of the `ForallInt32Instantiation` rule.
///
/// The instantiation guard `2 < exit` follows from `not (exit < 3)`, but
/// only through the frozen condition checker, which does not report the
/// premises it consumed. The rule therefore refuses the instantiation rather
/// than retaining evidence with no premise, which would make
/// `checks_atomic_derivation` vacuous for that guard. Restoring it is the
/// evidence-checked `decide` that the kernel authority boundary defers; when
/// that lands, this test should start selecting the instantiation again and
/// name `not (exit < 3)` as the guard premise.
#[test]
fn a_quantified_instantiation_guard_needing_a_derivation_is_refused() {
    let memory = SymbolicMemory::new();
    let data = Address {
        base: "refused-guard-data".into(),
        offset: AddressOffset::Constant(0),
    };
    let index = Variable(2_100_400);
    let exit = MachineTerm::Variable(Variable(2_100_401));
    let indexed_load = |value| {
        MachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
            Box::new(data.offset_by_int32_elements(value)),
            crate::kernel::LoadKind::Int32,
        )
    };
    let quantified = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(MachineTerm::Variable(index), exit.clone()),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(
                    indexed_load(MachineTerm::Variable(index)),
                    MachineTerm::Variable(index),
                ),
                true,
            )),
        ),
    );
    // `not (exit < 3)` entails `2 < exit`, but not exactly.
    let derivable_guard_source = Proposition::condition_is(
        ConditionTerm::signed_less_than(exit, MachineTerm::constant(3)),
        false,
    );
    let goal = Proposition::condition_is(
        ConditionTerm::equal(
            indexed_load(MachineTerm::constant(2)),
            MachineTerm::constant(2),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(quantified)
        .assume_proposition(derivable_guard_source);

    let retained =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .and_then(|derivation| derivation.forall_int32_instantiation().map(|_| ()));
    assert!(
        retained.is_none(),
        "an instantiation guard that needs a derivation must not be retained \
         as evidence whose premise list cannot name what discharged it"
    );
}

#[test]
fn quantified_int32_fact_certifies_a_concrete_indexed_load() {
    let memory = SymbolicMemory::new();
    let data = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let index = Variable(2_100_003);
    let index_term = MachineTerm::Variable(index);
    let indexed_load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
        Box::new(data.offset_by_int32_elements(index_term.clone())),
        crate::kernel::LoadKind::Int32,
    );
    let guarded_fact = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_equal(MachineTerm::constant(0), index_term.clone()),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_than(index_term.clone(), MachineTerm::constant(3)),
                    true,
                )),
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(indexed_load, index_term),
                true,
            )),
        ),
    );
    let concrete_index = MachineTerm::constant(1);
    let target = Proposition::condition_is(
        ConditionTerm::equal(
            MachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
                Box::new(data.offset_by_int32_elements(concrete_index.clone())),
                crate::kernel::LoadKind::Int32,
            ),
            concrete_index,
        ),
        true,
    );

    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new().assume_proposition(guarded_fact)),
        &target
    ));
}

#[test]
fn quantified_copy_fact_certifies_concrete_pointer_indices() {
    let memory = SymbolicMemory::new();
    let destination = Address {
        base: "argument-memory".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(2_200_000)), 4),
    };
    let source = Address {
        base: "argument-memory".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(2_200_001)), 4),
    };
    let index = Variable(2_200_002);
    let index_term = MachineTerm::Variable(index);
    let load = |base: &Address, index: MachineTerm| {
        MachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
            Box::new(base.offset_by_int32_elements(index)),
            crate::kernel::LoadKind::Int32,
        )
    };
    let copied = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_equal(MachineTerm::constant(0), index_term.clone()),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_than(index_term.clone(), MachineTerm::constant(3)),
                    true,
                )),
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(
                    load(&destination, index_term.clone()),
                    load(&source, index_term),
                ),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new().assume_proposition(copied);

    for index in [0, 1] {
        let index = MachineTerm::constant(index);
        assert!(crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &Proposition::condition_is(
                ConditionTerm::equal(load(&destination, index.clone()), load(&source, index),),
                true,
            )
        ));
    }
}

#[test]
fn quantified_int32_fact_does_not_certify_its_complete_guarded_range() {
    let memory = SymbolicMemory::new();
    let data = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let index = Variable(2_100_010);
    let length = MachineTerm::Variable(Variable(2_100_011));
    let index_bits = MachineTerm::Variable(index);
    let loaded_value = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
        Box::new(data.offset_by_int32_elements(index_bits.clone())),
        crate::kernel::LoadKind::Int32,
    );
    let guarded_fact = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_equal(MachineTerm::constant(0), index_bits.clone()),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_than(index_bits, length.clone()),
                    true,
                )),
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(loaded_value, MachineTerm::constant(7)),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new().assume_proposition(guarded_fact);
    let target = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: (MachineTerm::multiply(length.clone(), MachineTerm::constant(4))).into(),
        wide: false,
    };

    assert!(
        !crate::kernel::search::ProofSearch::proves(&(assumptions), &target),
        "a logical value fact cannot grant viewability"
    );
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: memory.with_block("other-state", 4),
            base: data.clone(),
            bytes: (MachineTerm::multiply(length.clone(), MachineTerm::constant(4))).into(),
            wide: false,
        }
    ));
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: SymbolicMemory::new(),
            base: Address {
                base: "other-data".into(),
                offset: AddressOffset::Constant(0),
            },
            bytes: (MachineTerm::multiply(length, MachineTerm::constant(4))).into(),
            wide: false,
        }
    ));
}

#[test]
fn proposition_derivation_check_requires_its_context() {
    let x = MachineTerm::Variable(Variable(86));
    let proposition = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(x, MachineTerm::constant(0)),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(proposition.clone());
    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &proposition)
            .expect("exact fact should produce a derivation");

    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
    assert_eq!(derivation.context_premises(), vec![proposition]);
}

#[test]
fn implication_derivation_context_excludes_its_local_antecedent() {
    let antecedent = Proposition::Predicate {
        name: "local_hypothesis".to_string(),
        arguments: Vec::new(),
    };
    let goal = Proposition::Implies(Box::new(antecedent.clone()), Box::new(antecedent));
    let assumptions = PureFactContext::new();
    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("an implication may use its own antecedent");

    assert!(derivation.check(&assumptions));
    assert!(
        derivation.context_premises().is_empty(),
        "binder-local assumptions are not ambient certificate premises"
    );
}

#[test]
fn forall_introduction_rejects_a_variable_free_in_ambient_assumptions() {
    let variable = Variable(186);
    let body = Proposition::Predicate {
        name: "holds".to_string(),
        arguments: vec![Term::Bitvector32(MachineTerm::Variable(variable).into())],
    };
    let goal = forall_int32(variable, body.clone());
    let assumptions = PureFactContext::new().assume_proposition(body);

    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &goal
    ));
    assert!(
        crate::kernel::search::ProofSearch::derive_proposition(&(assumptions), &goal).is_none()
    );
}

#[test]
fn forall_derivation_check_shadows_ambient_uses_of_the_binder_id() {
    let variable = Variable(187);
    let value = MachineTerm::Variable(variable);
    let goal = forall_int32(
        variable,
        Proposition::condition_is(ConditionTerm::equal(value.clone(), value), true),
    );
    let derivation =
        crate::kernel::search::ProofSearch::derive_proposition(&(PureFactContext::new()), &goal)
            .expect("reflexivity should prove a universal in an empty context");
    let contaminated = PureFactContext::new().assume_proposition(Proposition::Predicate {
        name: "ambient".to_string(),
        arguments: vec![Term::Bitvector32(MachineTerm::Variable(variable).into())],
    });

    assert!(derivation.check(&PureFactContext::new()));
    assert!(derivation.check(&contaminated));
}

#[test]
fn forall_introduction_keeps_outer_facts_when_the_body_ignores_the_binder() {
    let bound = MachineTerm::Variable(Variable(188));
    let left = MachineTerm::Variable(Variable(189));
    let middle = MachineTerm::Variable(Variable(190));
    let right = MachineTerm::Variable(Variable(191));
    let equality = |a, b| Proposition::condition_is(ConditionTerm::equal(a, b), true);
    let goal = forall_int32(Variable(188), equality(left.clone(), right.clone()));
    let first = equality(left.clone(), middle.clone());
    let second = equality(middle, right);
    let outer = equality(bound, left);
    let assumptions = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second.clone())
        .assume_proposition(outer.clone());

    let derivation = crate::kernel::search::ProofSearch::derive_proposition(&(assumptions), &goal)
        .expect("the binder-free body can use outer facts without weakening the context");
    assert!(derivation.check(&assumptions));
    assert_eq!(derivation.context_premises(), vec![outer, first, second]);
}

#[test]
fn singleton_substitution_derivation_records_only_its_bound_premises() {
    let variable = Variable(87);
    let value = MachineTerm::Variable(variable);
    let lower = Proposition::condition_is(
        ConditionTerm::signed_less_equal(MachineTerm::constant(3), value.clone()),
        true,
    );
    let upper = Proposition::condition_is(
        ConditionTerm::signed_less_equal(value.clone(), MachineTerm::constant(3)),
        true,
    );
    let goal =
        Proposition::condition_is(ConditionTerm::equal(value, MachineTerm::constant(3)), true);
    let unrelated = Proposition::Predicate {
        name: "unrelated".to_string(),
        arguments: vec![],
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(lower.clone())
        .assume_proposition(upper.clone())
        .assume_proposition(unrelated);
    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("singleton bounds should establish equality");

    assert!(matches!(
        &derivation.rule,
        PropositionDerivationRule::SingletonSubstitution { .. }
    ));
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
    let context = derivation.context_premises();
    assert_eq!(context, vec![lower, upper]);

    // The planner and checker both refuse an exhausted substitution; a
    // transient refusal must not become a proof or poison later checks.
    use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};
    let ((planned, checked), _) = instrumentation::with_tactic_work_limits(
        TacticWorkLimits {
            simple: 0,
            smart: 0,
            control: 0,
        },
        || {
            instrumentation::collect(|| {
                let tactic = TacticEvent {
                    source_tactic_path: None,
                    claim: "singleton certificate budget".into(),
                    tactic_index: 0,
                    tactic_name: "singleton_certificate_budget".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                let result = (
                    crate::kernel::search::ProofSearch::derive_by_singleton_substitution(
                        &(assumptions),
                        &goal,
                        true,
                    ),
                    derivation.check(&assumptions),
                );
                instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                result
            })
        },
    );
    assert!(planned.is_none());
    assert!(!checked);
    assert!(derivation.check(&assumptions));
}

#[test]
fn successor_order_derivation_needs_only_an_upper_bound() {
    let index = MachineTerm::Variable(Variable(88));
    let upper = MachineTerm::Variable(Variable(89));
    let upper_bound =
        Proposition::condition_is(ConditionTerm::signed_less_than(index.clone(), upper), true);
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_than(
            index.clone(),
            MachineTerm::add(index.clone(), MachineTerm::constant(1)),
        ),
        true,
    );
    let unrelated_order = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(
            MachineTerm::Variable(Variable(90)),
            MachineTerm::constant(0),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(unrelated_order)
        .assume_proposition(upper_bound.clone())
        .assume_proposition(Proposition::Predicate {
            name: "unrelated".to_string(),
            arguments: Vec::new(),
        });
    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("an int32 value below another int32 value cannot overflow when incremented");

    assert!(derivation.check(&assumptions));
    assert_eq!(derivation.context_premises(), vec![upper_bound]);
}

#[test]
fn upper_bound_extends_to_a_nonoverflowing_successor() {
    let length = MachineTerm::Variable(Variable(89_100));
    let capacity = MachineTerm::Variable(Variable(89_101));
    let successor = MachineTerm::add(capacity.clone(), MachineTerm::constant(1));
    let goal = ConditionTerm::signed_less_equal(length.clone(), successor.clone());
    let bounded = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(length, capacity.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(capacity.clone(), MachineTerm::constant(100)),
            true,
        );

    assert_eq!(
        bounded.decide(&ConditionTerm::signed_less_equal(
            MachineTerm::Variable(Variable(89_100)),
            capacity.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        bounded.decide(&ConditionTerm::signed_add_overflows(
            capacity.clone(),
            MachineTerm::constant(1),
        )),
        Some(false)
    );
    assert_eq!(bounded.decide(&goal), Some(true));
    assert_eq!(
        PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    MachineTerm::Variable(Variable(89_100)),
                    capacity,
                ),
                true,
            )
            .decide(&ConditionTerm::signed_less_equal(
                MachineTerm::Variable(Variable(89_100)),
                successor,
            )),
        None,
        "the successor relation must still require overflow evidence"
    );
}

/// A range's `fits` guard is the unsigned `count <=u limit`, which the kernel
/// encodes with a sign-bit bias. With the limit below the sign bit it means
/// `0 <= count` and `count <= limit`, and the condition checker decides it by
/// those two signed conditions, including through an order chain such as
/// `i <= n` and `n <= 1073741823`. A signed upper bound alone does not decide
/// it: a negative count is a huge unsigned one.
#[test]
fn unsigned_span_bound_below_the_sign_bit_is_decided_by_signed_order() {
    let count = MachineTerm::Variable(Variable(89_200));
    let end = MachineTerm::Variable(Variable(89_201));
    let limit = MachineTerm::constant(1_073_741_823);
    let fits = ConditionTerm::unsigned_less_equal(count.clone(), limit.clone());
    let nonnegative = ConditionTerm::signed_less_equal(MachineTerm::constant(0), count.clone());
    let chained = PureFactContext::new()
        .assume_condition(nonnegative.clone(), true)
        .assume_condition(
            ConditionTerm::signed_less_equal(count.clone(), end.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(end, limit.clone()), true);
    assert_eq!(chained.decide(&fits), Some(true));

    let upper_only = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(count.clone(), limit.clone()),
        true,
    );
    assert_eq!(
        upper_only.decide(&fits),
        None,
        "a count that may be negative is not below an unsigned limit"
    );

    let negative = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(count.clone(), MachineTerm::constant(0)),
        true,
    );
    assert_eq!(negative.decide(&fits), Some(false));

    let above = PureFactContext::new()
        .assume_condition(nonnegative, true)
        .assume_condition(ConditionTerm::signed_less_than(limit, count.clone()), true);
    assert_eq!(above.decide(&fits), Some(false));
}

/// A `uint32` bound below the sign bit on σ of a signed word, `(y as uint32)
/// <= c`, files its signed range on `y` itself: σ keeps `y`'s bits, so the
/// range is read through σ (one match at the root), never as a signed
/// comparison of the `uint32` term σ(y).
#[test]
fn a_sign_cast_bound_below_the_sign_bit_files_its_operand_s_signed_range() {
    let y = MachineTerm::Variable(Variable(89_210));
    let sigma = MachineTerm::sign_cast32(
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        y.clone(),
    );
    let limit = MachineTerm::constant(1_073_741_823);
    let context = PureFactContext::new().assume_condition(
        ConditionTerm::unsigned_less_equal(sigma.clone(), limit.clone()),
        true,
    );
    let zero = || MachineTerm::constant(0);
    let filed = |condition: ConditionTerm| {
        context.contains_assumed_exact(&Proposition::condition_is(condition, true))
    };
    assert!(filed(ConditionTerm::signed_less_equal(zero(), y.clone())));
    assert!(filed(ConditionTerm::signed_less_equal(
        y.clone(),
        limit.clone()
    )));
    assert!(!filed(ConditionTerm::signed_less_equal(
        zero(),
        sigma.clone()
    )));
    assert!(!filed(ConditionTerm::signed_less_equal(sigma, limit)));
    assert_eq!(
        context.decide(&ConditionTerm::signed_less_equal(zero(), y)),
        Some(true)
    );
}

/// A `uint32` order fact answers its mirrored spelling, as a signed one
/// does, and never the signed order of the same words.
#[test]
fn a_uint32_order_fact_answers_its_mirror_and_not_a_signed_order() {
    let x = MachineTerm::Variable(Variable(89_310));
    let y = MachineTerm::Variable(Variable(89_311));
    let context = PureFactContext::new().assume_condition(
        ConditionTerm::unsigned_less_than(x.clone(), y.clone()),
        true,
    );
    assert!(context.has_condition_fact(
        ConditionTerm::unsigned_greater_than(y.clone(), x.clone()),
        true
    ));
    assert_eq!(
        context.decide(&ConditionTerm::unsigned_greater_equal(x.clone(), y.clone())),
        Some(false)
    );
    assert!(
        !context.has_condition_fact(ConditionTerm::signed_less_than(x.clone(), y.clone()), true)
    );
    assert_eq!(context.decide(&ConditionTerm::signed_less_than(x, y)), None);
}

/// An unsigned chain `x <u n`, `n <=u 4` composes in the `uint32` order, so
/// it gives `x <u 4`, and with it the signed range
/// `0 <= x` and `x < 4` an index needs. It does not compose with a signed
/// bound on `n` (a negative `n` is a huge unsigned one), with no bound on
/// `n`, or through a wrapped `n - 1`.
#[test]
fn unsigned_order_chain_bounds_its_low_end_in_signed_order() {
    let x = MachineTerm::Variable(Variable(89_300));
    let n = MachineTerm::Variable(Variable(89_301));
    let four = MachineTerm::constant(4);
    let zero = MachineTerm::constant(0);
    let below_n = ConditionTerm::unsigned_less_than(x.clone(), n.clone());
    let nonnegative = ConditionTerm::signed_less_equal(zero.clone(), x.clone());
    let below_four = ConditionTerm::signed_less_than(x.clone(), four.clone());
    let chained = PureFactContext::new()
        .assume_condition(
            ConditionTerm::unsigned_less_equal(n.clone(), four.clone()),
            true,
        )
        .assume_condition(below_n.clone(), true);
    assert_eq!(
        chained.decide(&ConditionTerm::unsigned_less_than(x.clone(), four.clone())),
        Some(true)
    );
    assert_eq!(chained.decide(&nonnegative), Some(true));
    assert_eq!(chained.decide(&below_four), Some(true));
    assert_eq!(
        chained.decide(&ConditionTerm::signed_less_equal(x.clone(), four.clone())),
        Some(true)
    );
    assert_eq!(
        chained.decide(&ConditionTerm::signed_less_than(
            x.clone(),
            MachineTerm::constant(3)
        )),
        None,
        "`x <u 4` admits `x == 3`"
    );

    let signed_bound = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(n.clone(), four.clone()),
            true,
        )
        .assume_condition(below_n.clone(), true);
    assert_eq!(
        signed_bound.decide(&nonnegative),
        None,
        "a signed bound on `n` does not bound the unsigned `x <u n`"
    );
    assert_eq!(signed_bound.decide(&below_four), None);

    let unbounded = PureFactContext::new().assume_condition(below_n, true);
    assert_eq!(unbounded.decide(&nonnegative), None);
    assert_eq!(unbounded.decide(&below_four), None);

    let wrapped = PureFactContext::new()
        .assume_condition(
            ConditionTerm::unsigned_less_equal(n.clone(), four.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::unsigned_less_than(
                x.clone(),
                binary_node!(
                    Int32,
                    Subtract,
                    Box::new(n),
                    Box::new(MachineTerm::constant(1))
                ),
            ),
            true,
        );
    assert_eq!(
        wrapped.decide(&nonnegative),
        None,
        "`n - 1` wraps when `n` is zero"
    );
    assert_eq!(wrapped.decide(&below_four), None);
}

#[test]
fn assumptions_do_not_split_a_multi_value_context_variable() {
    let j = MachineTerm::Variable(Variable(87));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), MachineTerm::constant(2)),
            true,
        );
    let proposition = Proposition::Or(
        Box::new(Proposition::condition_is(
            ConditionTerm::equal(j.clone(), MachineTerm::constant(0)),
            true,
        )),
        Box::new(Proposition::condition_is(
            ConditionTerm::equal(j, MachineTerm::constant(1)),
            true,
        )),
    );

    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &proposition
    ));
    assert!(
        crate::kernel::search::ProofSearch::derive_proposition(&(assumptions), &proposition)
            .is_none()
    );
}

/// A finite universal's order fact reaches the order theory only through an
/// explicit instantiation.
///
/// From the kernel-search cleanup: the theory reads order facts
/// from `condition_facts`. Instantiating an ambient quantified fact inside an
/// order query was proof search in a theory checker; the `enumerate` step a
/// proof writes puts the instance where the theory can see it.
#[test]
fn finite_forall_order_fact_needs_an_explicit_instantiation() {
    let memory = SymbolicMemory::new();
    let indexed_load = |index| {
        MachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory(memory.clone()))),
            Box::new(Address {
                base: "arg-memory".into(),
                offset: AddressOffset::scale_int32(index, 4),
            }),
            crate::kernel::LoadKind::Int32,
        )
    };
    let k = Variable(88);
    let k_bits = MachineTerm::Variable(k);
    let load_k = indexed_load(k_bits.clone());
    let load_0 = indexed_load(MachineTerm::constant(0));
    let load_1 = indexed_load(MachineTerm::constant(1));
    let load_2 = indexed_load(MachineTerm::constant(2));
    let load_1_again = load_1.clone();
    let finite_order_fact = crate::kernel::quantifiers::test_forall(
        Default::default(),
        k,
        Sort::ProgramInt32,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_equal(MachineTerm::constant(0), k_bits.clone()),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_than(k_bits, MachineTerm::constant(1)),
                    true,
                )),
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_equal(load_k, load_1.clone()),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(finite_order_fact)
        .assume_condition(
            ConditionTerm::signed_less_equal(load_1, load_2.clone()),
            true,
        );

    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(load_0.clone(), load_2),
        true,
    );
    assert!(
        !crate::kernel::search::ProofSearch::proves(&(assumptions), &goal),
        "the quantified bound is not an order fact until it is instantiated"
    );

    // The condition fact an explicit `enumerate` instantiation contributes.
    let enumerated =
        assumptions.assume_condition(ConditionTerm::signed_less_equal(load_0, load_1_again), true);
    assert!(crate::kernel::search::ProofSearch::proves(
        &(enumerated),
        &goal
    ));
}

/// A guarded bound becomes an ordinary order fact when its exact guard holds.
///
/// The guard is exactly available, so unit propagation admits its conclusion
/// as an ordinary condition fact. The order theory can use that fact without
/// searching implication antecedents during its query.
#[test]
fn guarded_implication_bound_propagates_to_order_facts() {
    let a = MachineTerm::Variable(Variable(97_001));
    let b = MachineTerm::Variable(Variable(97_002));
    let c = MachineTerm::Variable(Variable(97_003));
    let guard = ConditionTerm::signed_less_than(
        MachineTerm::Variable(Variable(97_004)),
        MachineTerm::constant(10),
    );
    let a_le_b =
        Proposition::condition_is(ConditionTerm::signed_less_equal(a.clone(), b.clone()), true);
    let assumptions = PureFactContext::new()
        .assume_condition(guard.clone(), true)
        .assume_proposition(Proposition::Implies(
            Box::new(Proposition::condition_is(guard, true)),
            Box::new(a_le_b.clone()),
        ))
        .assume_condition(ConditionTerm::signed_less_equal(b, c.clone()), true);

    let goal = Proposition::condition_is(ConditionTerm::signed_less_equal(a, c), true);
    assert!(
        crate::kernel::search::ProofSearch::proves(&(assumptions), &goal),
        "an exactly satisfied guard publishes the bound to the order theory"
    );
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions.assume_proposition(a_le_b)),
        &goal
    ));
}

#[test]
fn conditional_forall_instantiates_at_same_named_variable_in_order_path() {
    let k = Variable(188);
    let k_bits = MachineTerm::Variable(k);
    let j = MachineTerm::Variable(Variable(189));
    let value_at_k = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
        Box::new(Address {
            base: "arg-memory".into(),
            offset: AddressOffset::scale_int32(k_bits.clone(), 4),
        }),
        crate::kernel::LoadKind::Int32,
    );
    let pivot = MachineTerm::Variable(Variable(191));
    let successor = MachineTerm::Variable(Variable(192));
    let induction_hypothesis = crate::kernel::quantifiers::test_forall(
        Default::default(),
        k,
        Sort::ProgramInt32,
        Proposition::Implies(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(k_bits.clone(), j.clone()),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_equal(value_at_k.clone(), pivot.clone()),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(induction_hypothesis)
        .assume_condition(
            ConditionTerm::signed_less_than(
                k_bits.clone(),
                MachineTerm::add(j.clone(), MachineTerm::constant(1)),
            ),
            true,
        )
        .assume_condition(ConditionTerm::equal(k_bits, j.clone()), false)
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j, MachineTerm::constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(pivot, successor.clone()),
            true,
        );
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_equal(value_at_k, successor),
        true,
    );

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("quantified order instance should produce a simplifier derivation");
    assert_eq!(derivation.conclusion(), &goal);
    assert!(derivation.check(&assumptions));
}

#[test]
fn a_binder_name_never_distinguishes_two_universals() {
    use std::hash::{Hash, Hasher};
    let universal = |name: &str| {
        crate::kernel::quantifiers::test_forall(
            crate::kernel::BinderName::written(name),
            Variable(530),
            Sort::ProgramInt32,
            Proposition::condition_is(ConditionTerm::Constant(true), true),
        )
    };
    let hash = |proposition: &Proposition| {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        proposition.hash(&mut hasher);
        hasher.finish()
    };
    let (written, other, unnamed) = (universal("a"), universal("b"), universal(""));
    assert!(written == other && written == unnamed);
    assert_eq!(written.cmp(&other), std::cmp::Ordering::Equal);
    assert_eq!(hash(&written), hash(&other));
    assert_eq!(hash(&written), hash(&unnamed));
    let facts = crate::kernel::proof::PureFactStore::from_ordered(&[written]);
    assert!(facts.contains(&other));
}

#[test]
fn forall_int32_instantiation_concludes_the_exact_substituted_body() {
    let binder = Variable(500);
    let bound = MachineTerm::Variable(binder);
    let premise = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(bound.clone(), MachineTerm::constant(0)),
        true,
    );
    let conclusion = Proposition::condition_is(ConditionTerm::equal(bound.clone(), bound), true);
    let quantified = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::ProgramInt32,
        Proposition::Implies(Box::new(premise), Box::new(conclusion)),
    );
    let value = MachineTerm::Variable(Variable(501));
    let instantiated_premise = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(value.clone(), MachineTerm::constant(0)),
        true,
    );
    let instantiated_conclusion =
        Proposition::condition_is(ConditionTerm::equal(value.clone(), value.clone()), true);
    let argument = InstanceArgument::Machine(value);

    assert_eq!(
        instantiate_universal(&quantified, &argument).ok(),
        Some(Proposition::Implies(
            Box::new(instantiated_premise.clone()),
            Box::new(instantiated_conclusion.clone()),
        ))
    );
    assert_eq!(
        check_forall_instantiation(
            &quantified,
            &argument,
            std::slice::from_ref(&instantiated_premise),
        )
        .ok(),
        Some(instantiated_conclusion)
    );
}

#[test]
fn forall_int32_instantiation_rejects_a_premise_that_does_not_give_its_guard() {
    // `v >= -1` (the signed reading of `u32::MAX`) does not give `v >= 0`.
    let binder = Variable(510);
    let bound = MachineTerm::Variable(binder);
    let quantified = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::ProgramInt32,
        Proposition::Implies(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_greater_equal(bound.clone(), MachineTerm::constant(0)),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(bound.clone(), bound),
                true,
            )),
        ),
    );
    let wrong = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(
            MachineTerm::Variable(Variable(511)),
            MachineTerm::constant(u32::MAX),
        ),
        true,
    );

    assert!(matches!(
        check_forall_instantiation(
            &quantified,
            &InstanceArgument::Machine(MachineTerm::Variable(Variable(511))),
            &[wrong],
        ),
        Err(ForallInstantiationError::MissingGuard(_))
    ));
}

#[test]
fn forall_int32_instantiation_avoids_capturing_the_argument_variable() {
    let outer = Variable(520);
    let inner = Variable(521);
    let quantified = crate::kernel::quantifiers::test_forall(
        Default::default(),
        outer,
        Sort::ProgramInt32,
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            inner,
            Sort::ProgramInt32,
            Proposition::condition_is(
                ConditionTerm::equal(MachineTerm::Variable(outer), MachineTerm::Variable(inner)),
                true,
            ),
        ),
    );
    let Ok(Proposition::ForAll {
        var: renamed, body, ..
    }) = instantiate_universal(
        &quantified,
        &InstanceArgument::Machine(MachineTerm::Variable(inner)),
    )
    else {
        panic!("nested quantifier should remain in the instance");
    };
    assert_ne!(*renamed, inner, "the inner binder must be renamed");
    assert!(
        matches!(&body.as_ref(), condition_source_0 @ Proposition::ConditionIs(
            _,
            true
        ) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::Equal, left, right }, _)) if (left.as_ref() == &MachineTerm::Variable(inner)
            && right.as_ref() == &MachineTerm::Variable(*renamed))))
    );
}

#[test]
fn forall_integer_instantiation_keeps_the_exact_guard_and_a_wide_argument() {
    let binder = Variable(600);
    let bound = IntegerTerm::var(binder);
    let premise = Proposition::condition_is(
        ConditionTerm::IntegerGreaterEqual(
            bound.clone().into(),
            IntegerTerm::constant_i64(0).into(),
        ),
        true,
    );
    let conclusion = Proposition::condition_is(
        ConditionTerm::IntegerEqual(bound.clone().into(), bound.clone().into()),
        true,
    );
    let quantified = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::Integer,
        Proposition::Implies(Box::new(premise), Box::new(conclusion)),
    );
    let wide = IntegerTerm::parse_constant("340282366920938463463374607431768211457")
        .expect("wide integer constant");
    let instantiated_premise = Proposition::condition_is(
        ConditionTerm::IntegerGreaterEqual(
            wide.clone().into(),
            IntegerTerm::constant_i64(0).into(),
        ),
        true,
    );
    let instantiated_conclusion = Proposition::condition_is(
        ConditionTerm::IntegerEqual(wide.clone().into(), wide.clone().into()),
        true,
    );
    let argument = InstanceArgument::Integer(wide);
    assert_eq!(
        instantiate_universal(&quantified, &argument).ok(),
        Some(Proposition::Implies(
            Box::new(instantiated_premise.clone()),
            Box::new(instantiated_conclusion.clone()),
        ))
    );
    assert_eq!(
        check_forall_instantiation(
            &quantified,
            &argument,
            std::slice::from_ref(&instantiated_premise),
        )
        .ok(),
        Some(instantiated_conclusion)
    );
}

#[test]
fn forall_integer_instantiation_rejects_a_missing_guard_or_another_sort() {
    let binder = Variable(610);
    let bound = IntegerTerm::var(binder);
    let guard = Proposition::condition_is(
        ConditionTerm::IntegerGreaterEqual(
            bound.clone().into(),
            IntegerTerm::constant_i64(0).into(),
        ),
        true,
    );
    let quantified = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::Integer,
        Proposition::Implies(
            Box::new(guard),
            Box::new(Proposition::condition_is(
                ConditionTerm::IntegerEqual(bound.clone().into(), bound.into()),
                true,
            )),
        ),
    );
    let value = InstanceArgument::Integer(IntegerTerm::var(Variable(612)));
    let changed = Proposition::condition_is(
        ConditionTerm::IntegerGreaterEqual(
            IntegerTerm::var(Variable(612)).into(),
            IntegerTerm::constant_i64(1).into(),
        ),
        true,
    );
    assert!(matches!(
        check_forall_instantiation(&quantified, &value, &[]),
        Err(ForallInstantiationError::MissingGuard(_))
    ));
    assert!(matches!(
        check_forall_instantiation(&quantified, &value, &[changed]),
        Err(ForallInstantiationError::MissingGuard(_))
    ));
    // An `Integer` binder takes no machine value, and a machine binder no
    // `Integer` term.
    assert!(matches!(
        instantiate_universal(
            &quantified,
            &InstanceArgument::Machine(MachineTerm::constant(4))
        ),
        Err(ForallInstantiationError::ArgumentSort)
    ));
    let machine = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::ProgramInt32,
        Proposition::condition_is(ConditionTerm::Constant(true), true),
    );
    assert!(matches!(
        instantiate_universal(
            &machine,
            &InstanceArgument::Integer(IntegerTerm::constant_i64(4))
        ),
        Err(ForallInstantiationError::ArgumentSort)
    ));
}

#[test]
fn forall_integer_instantiation_renames_nested_forall_and_exists_once() {
    let outer = Variable(620);
    let repeated = Variable(621);
    let body = crate::kernel::quantifiers::test_forall(
        Default::default(),
        repeated,
        Sort::Integer,
        crate::kernel::quantifiers::test_exists(
            "repeated".into(),
            repeated,
            Sort::Integer,
            Proposition::condition_is(
                ConditionTerm::IntegerEqual(
                    IntegerTerm::var(outer).into(),
                    IntegerTerm::var(repeated).into(),
                ),
                true,
            ),
        ),
    );
    let quantified =
        crate::kernel::quantifiers::test_forall(Default::default(), outer, Sort::Integer, body);
    let Ok(Proposition::ForAll {
        var: renamed_forall,
        body,
        ..
    }) = instantiate_universal(
        &quantified,
        &InstanceArgument::Integer(IntegerTerm::var(repeated)),
    )
    else {
        panic!("nested forall should remain in the instance");
    };
    let Proposition::Exists {
        var: renamed_exists,
        body,
        ..
    } = body.as_ref()
    else {
        panic!("nested exists should remain in the instance");
    };
    assert_ne!(*renamed_forall, repeated);
    assert_ne!(**renamed_exists, repeated);
    assert_ne!(renamed_forall, *renamed_exists);
    assert!(
        matches!(&body.as_ref(), condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::IntegerEqual(left, right), _)) if (left.as_ref() == &IntegerTerm::var(repeated)
                && right.as_ref() == &IntegerTerm::var(**renamed_exists))))
    );
}

#[test]
fn forall_integer_instantiation_supports_nested_machine_sorts_and_refuses_unsupported_carriers() {
    let binder = Variable(630);
    let one = InstanceArgument::Integer(IntegerTerm::constant_i64(1));
    let unsupported = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::Integer,
        Proposition::Predicate {
            name: "unsupported_integer_application".into(),
            arguments: vec![],
        },
    );
    assert!(matches!(
        instantiate_universal(&unsupported, &one),
        Err(ForallInstantiationError::SubstitutionRefused(_))
    ));
    let nested_machine_sort = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::Integer,
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            Variable(631),
            Sort::ProgramInt32,
            Proposition::condition_is(
                ConditionTerm::IntegerEqual(
                    IntegerTerm::var(binder).into(),
                    IntegerTerm::constant_i64(0).into(),
                ),
                true,
            ),
        ),
    );
    assert!(instantiate_universal(&nested_machine_sort, &one).is_ok());

    let true_body = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::Integer,
        Proposition::condition_is(ConditionTerm::Constant(true), true),
    );
    assert!(instantiate_universal(&true_body, &one).is_ok());
}

#[test]
fn forall_integer_instantiation_refuses_after_work_exhaustion() {
    let quantified = nested_integer_forall(16, false);
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 4,
        smart: 4,
        control: 4,
    };
    crate::instrumentation::with_tactic_work_limits(limits, || {
        let tactic = crate::instrumentation::TacticEvent {
            source_tactic_path: None,
            claim: "integer.quantifier".into(),
            tactic_index: 0,
            tactic_name: "integer_forall".into(),
            class: "simple".into(),
            statement_index: 0,
            source_index: 0,
        };
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticStarted(
            tactic.clone(),
        ));
        let instance = instantiate_universal(
            &quantified,
            &InstanceArgument::Integer(IntegerTerm::constant_i64(7)),
        );
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticFinished {
            tactic,
            elapsed: std::time::Duration::ZERO,
            work: 0,
        });
        assert!(
            instance.is_err(),
            "work exhaustion must not produce an instance"
        );
    });
}

#[test]
fn forall_pointer_instantiation_takes_a_pointer_of_the_binder_type() {
    let binder = Variable(640);
    let pointer = |variable, program_type| Pointer::new(Address::symbolic(variable), program_type);
    let pointer_term = |variable| {
        Term::ProgramValue(
            ProgramValue::Pointer(pointer(variable, ProgramType::Int32Pointer)).into(),
        )
    };
    let quantified = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::ProgramPointer(ProgramType::Int32Pointer),
        Proposition::Equal(pointer_term(binder), pointer_term(binder)),
    );
    let argument = InstanceArgument::Pointer(pointer(Variable(641), ProgramType::Int32Pointer));
    assert_eq!(
        check_forall_instantiation(&quantified, &argument, &[]).ok(),
        Some(Proposition::Equal(
            pointer_term(Variable(641)),
            pointer_term(Variable(641))
        ))
    );
    assert!(matches!(
        instantiate_universal(
            &quantified,
            &InstanceArgument::Pointer(pointer(Variable(641), ProgramType::UInt8Pointer)),
        ),
        Err(ForallInstantiationError::ArgumentSort)
    ));
    assert!(matches!(
        instantiate_universal(
            &quantified,
            &InstanceArgument::Machine(MachineTerm::constant(0))
        ),
        Err(ForallInstantiationError::ArgumentSort)
    ));
}

fn nested_integer_forall(depth: usize, capture: bool) -> Proposition {
    let outer = Variable(700);
    let mut body = Proposition::condition_is(
        ConditionTerm::IntegerEqual(
            IntegerTerm::var(outer).into(),
            IntegerTerm::constant_i64(0).into(),
        ),
        true,
    );
    for index in (0..depth).rev() {
        let var = if capture {
            Variable(701)
        } else {
            Variable(701 + index as u64)
        };
        body =
            crate::kernel::quantifiers::test_forall(Default::default(), var, Sort::Integer, body);
    }
    crate::kernel::quantifiers::test_forall(Default::default(), outer, Sort::Integer, body)
}

#[test]
fn simultaneous_proposition_substitution_does_not_rewrite_installed_values() {
    let first = Variable(540);
    let second = Variable(541);
    let proposition = Proposition::Implies(
        Box::new(Proposition::condition_is(
            ConditionTerm::equal(MachineTerm::Variable(first), MachineTerm::constant(5)),
            true,
        )),
        Box::new(Proposition::condition_is(
            ConditionTerm::equal(MachineTerm::Variable(first), MachineTerm::Variable(second)),
            true,
        )),
    );
    let substitutions = BTreeMap::from([
        (first, MachineTerm::Variable(second)),
        (second, MachineTerm::constant(0)),
    ]);

    let substituted = substitute_bitvector_variables_in_proposition(&proposition, &substitutions);
    assert_eq!(
        substituted,
        Proposition::Implies(
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(MachineTerm::Variable(second), MachineTerm::constant(5),),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(MachineTerm::Variable(second), MachineTerm::constant(0),),
                true,
            )),
        )
    );
}

#[test]
fn alpha_equivalence_rejects_free_variable_capture() {
    let free = Variable(550);
    let left_binder = Variable(551);
    let right_binder = free;
    let left = crate::kernel::quantifiers::test_forall(
        Default::default(),
        left_binder,
        Sort::ProgramInt32,
        Proposition::condition_is(
            ConditionTerm::equal(MachineTerm::Variable(free), MachineTerm::constant(5)),
            true,
        ),
    );
    let right = crate::kernel::quantifiers::test_forall(
        Default::default(),
        right_binder,
        Sort::ProgramInt32,
        Proposition::condition_is(
            ConditionTerm::equal(MachineTerm::Variable(free), MachineTerm::constant(5)),
            true,
        ),
    );

    assert!(!propositions_alpha_equivalent(&left, &right));
}

#[test]
fn range_fold_substitution_renames_a_captured_binder() {
    let source = Variable(560);
    let accumulator = Variable(561);
    let item = Variable(562);
    let fold = MachineTerm::range_fold(
        MachineTerm::Variable(Variable(563)),
        MachineTerm::Variable(Variable(564)),
        MachineTerm::constant(0),
        accumulator,
        item,
        MachineTerm::add(
            MachineTerm::Variable(accumulator),
            MachineTerm::Variable(item),
        ),
    );
    let term = MachineTerm::add(MachineTerm::Variable(source), fold);

    let substituted = substitute_bitvector_variable(&term, source, &MachineTerm::Variable(item));
    let binary_term!(Int32, Add, left, fold) = &substituted else {
        panic!("substitution should preserve the outer addition");
    };
    let MachineTerm::RangeFold {
        accumulator: renamed_accumulator,
        item: renamed_item,
        body,
        ..
    } = fold.as_ref()
    else {
        panic!("substitution should preserve the symbolic range fold");
    };
    assert_eq!(left.as_ref(), &MachineTerm::Variable(item));
    assert_ne!(*renamed_item, item);
    assert_eq!(*renamed_accumulator, accumulator);
    assert_eq!(
        body.as_ref(),
        &MachineTerm::add(
            MachineTerm::Variable(accumulator),
            MachineTerm::Variable(*renamed_item),
        )
    );
}

#[test]
fn assumptions_prove_by_bounded_disjunction_cases() {
    let x = MachineTerm::Variable(Variable(89));
    let x_is_zero = Proposition::condition_is(
        ConditionTerm::equal(x.clone(), MachineTerm::constant(0)),
        true,
    );
    let x_is_one = Proposition::condition_is(
        ConditionTerm::equal(x.clone(), MachineTerm::constant(1)),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Or(
        Box::new(x_is_zero.clone()),
        Box::new(x_is_one.clone()),
    ));

    // The general prover does not eliminate disjunctions; the explicit
    // derivation still does.
    let proposition = Proposition::Or(Box::new(x_is_one), Box::new(x_is_zero));
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &proposition
    ));
    assert_checkable_derivation(&assumptions, &proposition);
}

#[test]
fn known_memory_block_bounds_prove_symbolic_element_access() {
    let index = Variable(91);
    let index_bits = MachineTerm::Variable(index);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index_bits.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index_bits.clone(), MachineTerm::constant(3)),
            true,
        );
    let memory = SymbolicMemory::new().with_block("local:a", 12);
    let pointer = SymbolicMemory::local_pointer("a").offset_by_int32_elements(index_bits);

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: pointer.clone(),
            bytes: (MachineTerm::constant(4)).into(),
            wide: false,
        }
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryCanStore {
            memory,
            pointer,
            byte_width: 4,
        }
    ));
}

#[test]
fn symbolic_int32_range_directly_proves_constant_element_loadable() {
    let memory = SymbolicMemory::new();
    let base = Address {
        base: "data".into(),
        offset: AddressOffset::Constant(0),
    };
    let length = MachineTerm::Variable(Variable(89));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(2), length.clone()),
            true,
        )
        // The range's element count has to be one whose four-byte span does
        // not wrap before it can be read as `length` elements.
        .assume_condition(
            ConditionTerm::signed_less_equal(
                length.clone(),
                MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4)),
            ),
            true,
        )
        .assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: (MachineTerm::multiply(length, MachineTerm::constant(4))).into(),
            wide: false,
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory,
            base: base.offset_by_int32_elements(MachineTerm::constant(1)),
            bytes: (MachineTerm::constant(4)).into(),
            wide: false,
        }
    ));
}

#[test]
fn assumptions_prove_forall_int32_array_range_body() {
    let index = Variable(90);
    let index_bits = MachineTerm::Variable(index);
    let memory = SymbolicMemory::new().with_block("block", 12);
    let base = Address {
        base: "block".into(),
        offset: AddressOffset::Constant(0),
    };
    let indexed_pointer = base.offset_by_int32_elements(index_bits.clone());
    let in_segment = Proposition::And(
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_greater_equal(index_bits.clone(), MachineTerm::constant(0)),
            true,
        )),
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_less_than(index_bits, MachineTerm::constant(3)),
            true,
        )),
    );
    let loadable_index = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: indexed_pointer,
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
        memory,
        base,
        bytes: (MachineTerm::constant(12)).into(),
        wide: false,
    });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &forall_int32(
            index,
            Proposition::Implies(Box::new(in_segment), Box::new(loadable_index)),
        )
    ));
}

#[test]
fn loadability_transports_to_state_with_symbolic_index_bounds() {
    let index = MachineTerm::Variable(Variable(190));
    let cursor = MachineTerm::Variable(Variable(191));
    let range_memory = SymbolicMemory::new();
    let state_memory = SymbolicMemory::new().with_block("local:j", 4);
    let base = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(0),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::MemoryLoadable {
            memory: range_memory,
            base: base.clone(),
            bytes: (MachineTerm::constant(12)).into(),
            wide: false,
        })
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), cursor.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(cursor.clone(), MachineTerm::constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(cursor, MachineTerm::constant(2)),
            false,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            index.clone(),
            MachineTerm::constant(3),
        )),
        Some(true)
    );
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: state_memory,
            base: base.offset_by_int32_elements(index),
            bytes: (MachineTerm::constant(4)).into(),
            wide: false,
        }
    ));
}

#[test]
fn loadability_same_base_span_uses_graph_for_byte_count() {
    let before = SymbolicMemory::new().with_block("effect-side", 4);
    let written = Address {
        base: "effect-side".into(),
        offset: AddressOffset::Constant(0),
    };
    let after = before
        .clone()
        .store(written.clone(), int32(MachineTerm::constant(7)));
    let base = Address::symbolic(Variable(90_301));
    let a = MachineTerm::Variable(Variable(90_302));
    let b = MachineTerm::Variable(Variable(90_303));
    let bytes = |value| MachineTerm::add(value, MachineTerm::constant(1));
    let fact = Proposition::MemoryLoadable {
        memory: before.clone(),
        base: base.clone(),
        bytes: (bytes(a.clone())).into(),
        wide: false,
    };
    let goal = Proposition::MemoryLoadable {
        memory: after.clone(),
        base: base.clone(),
        bytes: (bytes(b.clone())).into(),
        wide: false,
    };
    let premise = ConditionTerm::equal(a, b.clone());
    let without_premise = PureFactContext::new().assume_proposition(fact.clone());
    let with_premise = without_premise
        .clone()
        .assume_condition(premise.clone(), true);
    let _scope = with_premise.enter_id_scope();

    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(with_premise.proves_atomic_without_search(&goal));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    let derivation =
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(with_premise), &goal)
            .expect("the same-base loadable range should transport");
    assert!(derivation.check(&with_premise));
    assert!(!without_premise.proves_atomic_without_search(&goal));
    let without_loadable = PureFactContext::new().assume_condition(premise, true);
    assert!(!without_loadable.proves_atomic_without_search(&goal));
    let other_base = Proposition::MemoryLoadable {
        memory: after,
        base: Address::symbolic(Variable(90_304)),
        bytes: (bytes(b)).into(),
        wide: false,
    };
    assert!(!with_premise.proves_atomic_without_search(&other_base));
}

/// `lower <= term and term < upper`.
fn int32_half_open_bound(term: &MachineTerm, lower: i64, upper: i64) -> Proposition {
    Proposition::And(
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_greater_equal(term.clone(), signed_i64_bitvector_constant(lower)),
            true,
        )),
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_less_than(term.clone(), signed_i64_bitvector_constant(upper)),
            true,
        )),
    )
}

#[test]
fn finite_forall_rejects_a_bare_conjunct_beside_a_guarded_one() {
    // `forall k. ((0 <= k and k < 3) implies 0 <= k) and (k < 3)` is false at
    // k = 5: the guard bounds only its own implication, and the bare
    // conjunct is not vacuous anywhere, so no finite range justifies it.
    let k = Variable(92_100);
    let k_bits = MachineTerm::Variable(k);
    let guarded = Proposition::Implies(
        Box::new(int32_half_open_bound(&k_bits, 0, 3)),
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_greater_equal(k_bits.clone(), MachineTerm::constant(0)),
            true,
        )),
    );
    let bare = Proposition::condition_is(
        ConditionTerm::signed_less_than(k_bits.clone(), MachineTerm::constant(3)),
        true,
    );
    let body = Proposition::And(Box::new(guarded.clone()), Box::new(bare));

    assert!(finite_forall_ranges(&[k], &body).is_none());
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &forall_int32(k, body)
    ));
    // The guarded conjunct alone still derives by instantiation.
    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &forall_int32(k, guarded)
    ));
}

#[test]
fn finite_forall_instantiates_the_hull_of_every_guard() {
    // Two guards of different widths: the universal is vacuous only outside
    // the wider one, so instances must cover 0..=9, where `k < 5` fails at
    // k = 5 while `k < 10` holds throughout.
    let k = Variable(92_101);
    let k_bits = MachineTerm::Variable(k);
    let narrow = Proposition::Implies(
        Box::new(int32_half_open_bound(&k_bits, 0, 3)),
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_greater_equal(k_bits.clone(), MachineTerm::constant(0)),
            true,
        )),
    );
    let wide = |upper: u32| {
        Proposition::Implies(
            Box::new(int32_half_open_bound(&k_bits, 0, 10)),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(k_bits.clone(), MachineTerm::constant(upper)),
                true,
            )),
        )
    };
    let false_at_five = Proposition::And(Box::new(narrow.clone()), Box::new(wide(5)));
    let ranges = finite_forall_ranges(&[k], &false_at_five).expect("both leaves are guarded");
    assert_eq!((ranges[0].lower, ranges[0].upper), (0, 9));
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &forall_int32(k, false_at_five)
    ));

    let true_throughout = Proposition::And(Box::new(narrow), Box::new(wide(10)));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &forall_int32(k, true_throughout)
    ));
}

#[test]
fn assumptions_prove_finite_forall_int32_by_instantiation() {
    let i = Variable(92);
    let j = Variable(93);
    let i_bits = MachineTerm::Variable(i);
    let j_bits = MachineTerm::Variable(j);
    let antecedent = Proposition::And(
        Box::new(Proposition::And(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_greater_equal(i_bits.clone(), MachineTerm::constant(0)),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_greater_equal(j_bits.clone(), MachineTerm::constant(0)),
                true,
            )),
        )),
        Box::new(Proposition::And(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(i_bits.clone(), j_bits.clone()),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(j_bits, MachineTerm::constant(3)),
                true,
            )),
        )),
    );
    let consequent = Proposition::Or(
        Box::new(Proposition::condition_is(
            ConditionTerm::equal(i_bits.clone(), MachineTerm::constant(0)),
            true,
        )),
        Box::new(Proposition::condition_is(
            ConditionTerm::equal(i_bits, MachineTerm::constant(1)),
            true,
        )),
    );

    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &forall_int32(
            i,
            forall_int32(
                j,
                Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
            ),
        )
    ));
}

#[test]
fn assumptions_use_finite_forall_fact_to_prove_condition() {
    let k = Variable(94);
    let base_left = MachineTerm::Variable(Variable(95));
    let base_right = MachineTerm::Variable(Variable(96));
    let k_bits = MachineTerm::Variable(k);
    let antecedent = Proposition::And(
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_greater_equal(k_bits.clone(), MachineTerm::constant(0)),
            true,
        )),
        Box::new(Proposition::condition_is(
            ConditionTerm::signed_less_than(k_bits.clone(), MachineTerm::constant(3)),
            true,
        )),
    );
    let consequent = Proposition::condition_is(
        ConditionTerm::equal(
            binary_node!(
                Int32,
                Add,
                Box::new(base_left.clone()),
                Box::new(k_bits.clone())
            ),
            binary_node!(Int32, Add, Box::new(base_right.clone()), Box::new(k_bits)),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(forall_int32(
        k,
        Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
    ));

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::condition_is(
            ConditionTerm::equal(
                binary_node!(
                    Int32,
                    Add,
                    Box::new(base_left),
                    Box::new(MachineTerm::constant(1))
                ),
                binary_node!(
                    Int32,
                    Add,
                    Box::new(base_right),
                    Box::new(MachineTerm::constant(1))
                ),
            ),
            true,
        )
    ));
}

#[test]
fn order_solver_uses_negated_less_than_transitively() {
    let a = MachineTerm::Variable(Variable(94));
    let b = MachineTerm::Variable(Variable(95));
    let c = MachineTerm::Variable(Variable(96));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(b.clone(), a.clone()), false)
        .assume_condition(ConditionTerm::signed_less_than(c.clone(), b), false);

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::condition_is(ConditionTerm::signed_less_equal(a, c), true,)
    ));
}

#[test]
fn assumptions_do_not_prove_implication_by_treating_unknown_antecedent_as_false() {
    let x = MachineTerm::Variable(Variable(91));
    let antecedent = Proposition::condition_is(
        ConditionTerm::signed_greater_equal(x.clone(), MachineTerm::constant(0)),
        true,
    );
    let consequent =
        Proposition::condition_is(ConditionTerm::equal(x, MachineTerm::constant(0)), true);

    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &Proposition::Implies(Box::new(antecedent), Box::new(consequent),)
    ));
}

#[test]
fn assumptions_prove_implication_with_refuted_antecedent() {
    let x = MachineTerm::Variable(Variable(91));
    let condition = ConditionTerm::equal(x, MachineTerm::constant(0));
    let assumptions = PureFactContext::new().assume_condition(condition.clone(), true);
    let antecedent = Proposition::condition_is(condition, false);
    let consequent = Proposition::condition_is(
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(92)),
            MachineTerm::constant(7),
        ),
        true,
    );

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::Implies(Box::new(antecedent), Box::new(consequent),)
    ));
}

#[test]
fn solve_derives_vacuous_implication_before_searching_large_consequent() {
    fn unknown_tree(depth: usize, index: usize) -> Proposition {
        if depth == 0 {
            return Proposition::Predicate {
                name: format!("unknown_{index}"),
                arguments: Vec::new(),
            };
        }
        Proposition::And(
            Box::new(unknown_tree(depth - 1, index * 2)),
            Box::new(unknown_tree(depth - 1, index * 2 + 1)),
        )
    }

    let condition = ConditionTerm::equal(
        MachineTerm::Variable(Variable(93)),
        MachineTerm::constant(0),
    );
    let antecedent = Proposition::condition_is(condition.clone(), true);
    let consequent = unknown_tree(9, 0);
    let goal = Proposition::Implies(Box::new(antecedent), Box::new(consequent));
    let assumptions = PureFactContext::new().assume_condition(condition, false);

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("a refuted antecedent should close before inspecting the consequent");
    assert!(derivation.check(&assumptions));
}

#[test]
fn solve_derives_implication_body_before_refuting_known_antecedent() {
    let antecedent_condition = ConditionTerm::equal(
        MachineTerm::Variable(Variable(94)),
        MachineTerm::constant(0),
    );
    let consequent_condition = ConditionTerm::equal(
        MachineTerm::Variable(Variable(95)),
        MachineTerm::constant(7),
    );
    let goal = Proposition::Implies(
        Box::new(Proposition::condition_is(
            antecedent_condition.clone(),
            true,
        )),
        Box::new(Proposition::condition_is(
            consequent_condition.clone(),
            true,
        )),
    );
    let assumptions = PureFactContext::new()
        .assume_condition(antecedent_condition, true)
        .assume_condition(consequent_condition, true);

    let derivation =
        crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &goal)
            .expect("a known antecedent should use the available consequent directly");
    assert!(derivation.check(&assumptions));
}

#[test]
fn assumptions_simplify_overflow_through_equality_chain() {
    let index = MachineTerm::Variable(Variable(91));
    let length = MachineTerm::Variable(Variable(92));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(index.clone(), length.clone()), true)
        .assume_condition(ConditionTerm::equal(length, MachineTerm::constant(0)), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            index,
            MachineTerm::constant(1),
        )),
        Some(false),
    );
}

#[test]
fn same_block_pointer_equality_transports_through_equal_offsets() {
    let left = Address {
        base: "shared".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(91)), 4),
    };
    let right = Address {
        base: "shared".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(92)), 4),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::address_equal(left.clone(), right.clone()),
        true,
    );

    assert!(pointers_proven_equal_for_memory_resolution(
        &left.offset_by_int32_elements(MachineTerm::constant(1)),
        &right.offset_by_int32_elements(MachineTerm::constant(1)),
        &assumptions,
    ));
}

#[test]
fn symbolic_pointer_equality_needs_explicit_guarded_arithmetic() {
    let base = MachineTerm::Variable(Variable(100_000));
    let index = MachineTerm::Variable(Variable(1_000_000));
    let source_left = Address {
        base: AddressBase::Symbolic(Variable(1_000_001)),
        offset: AddressOffset::Constant(0),
    };
    let source_right = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Add(
            Box::new(AddressOffset::scale_int32(base.clone(), 4)),
            Box::new(AddressOffset::scale_int32(index.clone(), 4)),
        ),
    };
    let goal_left = source_left.offset_by_int32_elements(MachineTerm::constant(1));
    let goal_right = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Add(
            Box::new(AddressOffset::scale_int32(base, 4)),
            Box::new(AddressOffset::scale_int32(
                MachineTerm::add(index, MachineTerm::constant(1)),
                4,
            )),
        ),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::address_equal(source_left, source_right),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_add_overflows(
                MachineTerm::Variable(Variable(1_000_000)),
                MachineTerm::constant(1),
            ),
            false,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            MachineTerm::Variable(Variable(1_000_000)),
            MachineTerm::constant(1),
        )),
        Some(false),
    );
    // The graph does not distribute a scaled int32 addition merely because
    // the ambient context can prove its no-overflow guard. A proof can name
    // the pointer relation and guard in `arithmetic() using` instead.
    assert_eq!(
        assumptions.decide(&ConditionTerm::address_equal(goal_left, goal_right)),
        None,
    );
}

#[test]
fn builtin_obligation_solver_discharges_concrete_invariant() {
    let pointer = Address {
        base: "block".into(),
        offset: AddressOffset::Constant(0),
    };
    let memory = SymbolicMemory::new().with_block("block", 4);
    let invariant = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: pointer,
        bytes: (MachineTerm::constant(4)).into(),
        wide: false,
    };
    let state = ExecutionState::new()
        .with_local("x", int32(0))
        .with_memory(memory);
    let statement = program_while(
        crate::kernel::program_expression::greater_than(
            crate::kernel::program_expression::variable("x"),
            crate::kernel::program_expression::int32_literal(0),
        ),
        vec![invariant],
        program_assign(
            "x",
            crate::kernel::program_expression::subtract(
                crate::kernel::program_expression::variable("x"),
                crate::kernel::program_expression::int32_literal(1),
            ),
        ),
    );
    let theorem =
        prove_symbolic_program_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("concrete invariant should be solved");

    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: StatementOutcome::Normal(Box::new(state)),
        }
    );
}

#[test]
fn equality_rewrites_through_matching_decrement() {
    let left = MachineTerm::Variable(Variable(66_001));
    let right = MachineTerm::Variable(Variable(66_002));
    let equality =
        Proposition::condition_is(ConditionTerm::equal(left.clone(), right.clone()), true);
    let goal = Proposition::condition_is(
        ConditionTerm::equal(
            MachineTerm::subtract(left, MachineTerm::constant(1)),
            MachineTerm::subtract(right, MachineTerm::constant(1)),
        ),
        true,
    );

    assert!(
        crate::kernel::search::ProofSearch::derive_solve_proposition(
            &(PureFactContext::new().assume_proposition(equality)),
            &goal
        )
        .is_some()
    );
}

#[test]
fn symbolic_max_lt_branch_is_native_theorem() {
    let a = Variable(10);
    let b = Variable(11);
    let theorem = prove_program_max_lt_returns_right(a, b).expect("lt branch should prove");
    let condition = ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation: CompareRelation::LessThan,
        left: Box::new(MachineTerm::Variable(a)),
        right: Box::new(MachineTerm::Variable(b)),
    };
    let state = program_max_state(
        int32(MachineTerm::Variable(a)),
        int32(MachineTerm::Variable(b)),
    );

    assert_eq!(
        theorem.proposition(),
        &forall_int32(
            a,
            forall_int32(
                b,
                Proposition::Implies(
                    Box::new(Proposition::condition_is(condition, true)),
                    Box::new(Proposition::ProgramStatementVerifies {
                        state: Box::new(state.clone()),
                        statement: Box::new(program_max_body()),
                        outcome: StatementOutcome::Return {
                            value: int32(MachineTerm::Variable(b)).into(),
                            state: Box::new(state),
                        },
                    }),
                ),
            ),
        )
    );
}

#[test]
fn symbolic_max_not_lt_branch_is_native_theorem() {
    let a = Variable(12);
    let b = Variable(13);
    let theorem = prove_program_max_not_lt_returns_left(a, b).expect("false branch should prove");
    let condition = ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation: CompareRelation::LessThan,
        left: Box::new(MachineTerm::Variable(a)),
        right: Box::new(MachineTerm::Variable(b)),
    };
    let state = program_max_state(
        int32(MachineTerm::Variable(a)),
        int32(MachineTerm::Variable(b)),
    );

    assert_eq!(
        theorem.proposition(),
        &forall_int32(
            a,
            forall_int32(
                b,
                Proposition::Implies(
                    Box::new(Proposition::condition_is(condition, false)),
                    Box::new(Proposition::ProgramStatementVerifies {
                        state: Box::new(state.clone()),
                        statement: Box::new(program_max_body()),
                        outcome: StatementOutcome::Return {
                            value: int32(MachineTerm::Variable(a)).into(),
                            state: Box::new(state),
                        },
                    }),
                ),
            ),
        )
    );
}

#[test]
fn repeated_order_fact_collections_share_one_scan() {
    let left = MachineTerm::Variable(Variable(93_101));
    let right = MachineTerm::Variable(Variable(93_102));
    let assumptions =
        PureFactContext::new().assume_condition(ConditionTerm::signed_less_than(left, right), true);
    let _scope = assumptions.enter_id_scope();

    let first = assumptions.selected_for_test().condition_order_facts();
    let second = assumptions.selected_for_test().condition_order_facts();

    assert_eq!(first.len(), 1, "the order fact should be collected");
    assert!(
        std::rc::Rc::ptr_eq(&first, &second),
        "a repeated collection over one fact set should share the first scan"
    );
}

#[test]
fn repeated_resolution_queries_do_not_repay_their_search() {
    let left = Address {
        base: "memo-regression".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(93_103)), 4),
    };
    let right = Address {
        base: "memo-regression".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(93_104)), 4),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(
                MachineTerm::Variable(Variable(93_103)),
                MachineTerm::Variable(Variable(93_104)),
            ),
            true,
        )
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(memory_range(left.clone(), 0, 1))),
            right: Box::new(Resource::Memory(memory_range(right.clone(), 0, 1))),
        });
    let _scope = assumptions.enter_id_scope();

    let work_for = |index: usize, query: fn(&Address, &Address, &PureFactContext) -> bool| {
        let tactic = crate::instrumentation::TacticEvent {
            source_tactic_path: None,
            claim: "memo.regression".to_string(),
            tactic_index: index,
            tactic_name: "query".to_string(),
            class: "simple".to_string(),
            statement_index: index,
            source_index: index,
        };
        let (result, events) = crate::instrumentation::collect(|| {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticStarted(
                tactic.clone(),
            ));
            let result = query(&left, &right, &assumptions);
            crate::instrumentation::emit(
                crate::instrumentation::VerificationEvent::TacticFinished {
                    tactic: tactic.clone(),
                    elapsed: std::time::Duration::ZERO,
                    work: 0,
                },
            );
            result
        });
        let work = events
            .iter()
            .find_map(|event| match event {
                crate::instrumentation::VerificationEvent::TacticFinished { work, .. } => {
                    Some(*work)
                }
                _ => None,
            })
            .expect("the query tactic should finish");
        (result, work)
    };

    let (first_result, first_work) = work_for(0, pointers_proven_equal_for_memory_resolution);
    let (second_result, second_work) = work_for(1, pointers_proven_equal_for_memory_resolution);

    assert_eq!(
        first_result, second_result,
        "the memo must not change answers"
    );
    assert!(
        first_work > 0,
        "the first query should consume deterministic work"
    );
    assert_eq!(
        second_work, 0,
        "a repeated top-level query should answer from the memo without new work"
    );

    let (first_result, first_work) = work_for(2, pointers_proven_distinct_for_memory_resolution);
    let (second_result, second_work) = work_for(3, pointers_proven_distinct_for_memory_resolution);
    assert!(first_result && second_result);
    assert!(
        first_work > 0,
        "the first distinctness query should consume deterministic work"
    );
    assert_eq!(
        second_work, 0,
        "repeated top-level distinctness should share the resolution memo"
    );
}

#[test]
fn common_base_offset_distinctness_handles_the_unoffset_base() {
    let base = Address {
        base: "common-base".into(),
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(93_105)), 4),
    };
    let field = Address {
        base: base.base.clone(),
        offset: AddressOffset::add(base.offset.clone(), AddressOffset::Constant(4)),
    };
    let assumptions = PureFactContext::new();

    assert!(pointer_offsets_with_common_base_proven_distinct(
        &base,
        &field,
        &assumptions,
    ));
    assert!(pointer_offsets_with_common_base_proven_distinct(
        &field,
        &base,
        &assumptions,
    ));
}

/// A pointer that is its own block, such as one loaded from memory, indexes
/// with bare offsets: `p[i]` and `p[j]` add nothing else to the block, so the
/// whole offsets are the indices the common-base ladder compares.
#[test]
fn common_base_offset_distinctness_compares_bare_offsets_of_one_block() {
    let block = AddressBase::Symbolic(Variable(93_200));
    let element = |index: MachineTerm| Address {
        base: block.clone(),
        offset: AddressOffset::scale_int32(index, 4),
    };
    let i = MachineTerm::Variable(Variable(93_201));
    let j = MachineTerm::Variable(Variable(93_202));
    let ordered = PureFactContext::new().assume_proposition(Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(i.clone()),
            right: Box::new(j.clone()),
        },
        true,
    ));

    assert!(pointer_offsets_with_common_base_proven_distinct(
        &element(i.clone()),
        &element(j.clone()),
        &ordered,
    ));
    assert!(!pointer_offsets_with_common_base_proven_distinct(
        &element(i.clone()),
        &element(j),
        &PureFactContext::new(),
    ));
    let first = Address {
        base: block.clone(),
        offset: AddressOffset::Constant(0),
    };
    let second = Address {
        base: block,
        offset: AddressOffset::Constant(4),
    };
    assert!(pointer_offsets_with_common_base_proven_distinct(
        &first,
        &second,
        &PureFactContext::new(),
    ));
    assert!(!pointer_offsets_with_common_base_proven_distinct(
        &first,
        &first,
        &PureFactContext::new(),
    ));
}

/// Pins the non-structural fallback in context inconsistency. Equality classes
/// decide structural endpoints, but `x + y` and `y + x` are related only by
/// additive theory equality, which is not an equality-graph edge, so this
/// contradiction is reachable only through the retained pairwise comparison.
#[test]
fn derived_order_contradiction_uses_theory_equal_endpoints() {
    let x = MachineTerm::Variable(Variable(97_001));
    let y = MachineTerm::Variable(Variable(97_002));
    let middle = MachineTerm::Variable(Variable(97_003));
    let left_sum = MachineTerm::add(x.clone(), y.clone());
    let right_sum = MachineTerm::add(y, x);
    assert_ne!(
        left_sum, right_sum,
        "the endpoints must not be exactly equal, or the class check would decide them"
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(left_sum, middle.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(middle, right_sum), true);

    assert!(
        assumptions.is_inconsistent(),
        "`x + y < middle` and `middle < y + x` contradict through additive equality"
    );
}

/// Pins the load-resolution reach of the order-conflict fallback: a load whose
/// memory determines its value contradicts a strict order against that value.
/// The comparison enters through `memory_loads_proven_equal`'s resolution step,
/// not through any equality fact.
#[test]
fn derived_order_contradiction_resolves_load_endpoints() {
    let cell = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(0),
    };
    let memory = SymbolicMemory::new().store(cell.clone(), int32(MachineTerm::constant(7)));
    let load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
        Box::new(cell),
        crate::kernel::LoadKind::Int32,
    );
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(load, MachineTerm::constant(7)),
        true,
    );

    assert!(
        assumptions.is_inconsistent(),
        "a load that resolves to 7 cannot be strictly below 7"
    );
}

/// Pins the cross-state reach of the order-conflict fallback: loads of one
/// untouched cell from two states related by a recorded effect are equal,
/// so a strict order between them is a contradiction. Neither form is an
/// equality-graph edge.
#[test]
fn derived_order_contradiction_bridges_state_loads() {
    let preserved = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(0),
    };
    let written = Address {
        base: "arg-memory".into(),
        offset: AddressOffset::Constant(4),
    };
    // The untouched cell is the `int32` at offset zero; a width-less load
    // there spans eight bytes and the store at offset four does touch it.
    crate::kernel::eval::declare_load_access_width(&preserved, 4);
    let before = SymbolicMemory::new();
    let after = before
        .clone()
        .store(written.clone(), int32(MachineTerm::constant(1)));
    let before_load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(before.clone()))),
        Box::new(preserved.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let after_load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory(after.clone()))),
        Box::new(preserved),
        crate::kernel::LoadKind::Int32,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::MemoryMutatesOnly {
            before,
            after,
            writes: vec![(written, crate::kernel::AccessExtent::from(4))],
        })
        .assume_condition(
            ConditionTerm::signed_less_than(after_load, before_load),
            true,
        );

    assert!(
        assumptions.is_inconsistent(),
        "loads of an untouched cell across a recorded effect are equal"
    );
}

/// Signed intervals are reconstructed over the term's structure with no
/// depth cut: a sum of any depth over a bounded variable ranges.
#[test]
fn signed_intervals_range_sums_of_any_depth() {
    let x = MachineTerm::Variable(Variable(7_200_000));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(x.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(x.clone(), MachineTerm::constant(1)),
            true,
        );
    for depth in [8, 32, 64, 128] {
        let mut sum = x.clone();
        for _ in 0..depth {
            sum = binary_node!(Int32, Add, Box::new(sum), Box::new(x.clone()));
        }
        assert_eq!(
            assumptions.decide_from_overflow_facts(&ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: Box::new(sum),
                right: Box::new(x.clone())
            }),
            Some(false),
            "a {depth}-deep sum of a variable in [0, 1] cannot overflow"
        );
    }
}

/// The constant-normalization walk has no node budget: a constant reached
/// through a chain of equalities of any length resolves, since the walk
/// resolves each term once.
#[test]
fn constant_normalization_follows_equality_chains_of_any_length() {
    for length in [16u64, 32, 64, 128] {
        let variable = |index: u64| MachineTerm::Variable(Variable(7_300_000 + index));
        let mut assumptions = PureFactContext::new();
        for index in 0..length {
            let next = if index + 1 == length {
                MachineTerm::constant(length as u32)
            } else {
                variable(index + 1)
            };
            assumptions =
                assumptions.assume_condition(ConditionTerm::equal(variable(index), next), true);
        }
        assert_eq!(
            assumptions.signed_constant_after_equality_normalization(&variable(0)),
            Some(length as i64),
            "a chain of {length} equalities resolves to its constant"
        );
    }
}

/// A solve derivation has no step budget: a balanced conjunction of any
/// width whose parts are exact facts derives, its work following the goal.
#[test]
fn solve_derivations_have_no_step_budget() {
    for width in [64u64, 128, 256, 512] {
        let variable = |index: u64| MachineTerm::Variable(Variable(7_500_000 + index));
        let condition =
            |index: u64| ConditionTerm::equal(variable(index), MachineTerm::constant(index as u32));
        let mut assumptions = PureFactContext::new();
        for index in 0..width {
            assumptions = assumptions.assume_condition(condition(index), true);
        }
        let mut parts = (0..width)
            .map(|index| Proposition::condition_is(condition(index), true))
            .collect::<Vec<_>>();
        while parts.len() > 1 {
            parts = parts
                .chunks(2)
                .map(|pair| match pair {
                    [left, right] => {
                        Proposition::And(Box::new(left.clone()), Box::new(right.clone()))
                    }
                    [single] => single.clone(),
                    _ => unreachable!(),
                })
                .collect();
        }
        assert!(
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(assumptions), &parts[0])
                .is_some(),
            "a conjunction of {width} exact facts derives"
        );
    }
}

/// Finite quantifiers instantiate over domains of any width: the instances
/// are the quantifier's own bounds, charged as deterministic work, and a
/// disjunctive consequent that only instantiation decides is proved for a
/// domain wider than the old cap of 128.
#[test]
fn finite_forall_instantiates_domains_of_any_width() {
    for width in [129i64, 200, 400] {
        let i = Variable(7_600_000);
        let i_bits = MachineTerm::Variable(i);
        let antecedent = Proposition::And(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_greater_equal(i_bits.clone(), MachineTerm::constant(0)),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(
                    i_bits.clone(),
                    MachineTerm::constant(width as u32),
                ),
                true,
            )),
        );
        // A balanced disjunction: its depth is logarithmic in the width, so
        // the width is what the proof exercises.
        let mut cases = (0..width)
            .map(|value| {
                Proposition::condition_is(
                    ConditionTerm::equal(i_bits.clone(), MachineTerm::constant(value as u32)),
                    true,
                )
            })
            .collect::<Vec<_>>();
        while cases.len() > 1 {
            cases = cases
                .chunks(2)
                .map(|pair| match pair {
                    [left, right] => {
                        Proposition::Or(Box::new(left.clone()), Box::new(right.clone()))
                    }
                    [single] => single.clone(),
                    _ => unreachable!(),
                })
                .collect();
        }
        let consequent = cases.remove(0);
        let goal = forall_int32(
            i,
            Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
        );
        assert!(
            crate::kernel::search::ProofSearch::proves(&(PureFactContext::new()), &goal),
            "a domain of {width} values instantiates"
        );
    }
}

/// Disjunction facts of any width eliminate: the cases are the fact's own
/// disjuncts, and a disjunction of 12 to 48 cases, each proving the goal,
/// derives it, which the old cap of eight cases refused.
#[test]
fn disjunction_cases_of_any_width_derive_a_common_consequence() {
    for width in [12u32, 24, 48] {
        let x = MachineTerm::Variable(Variable(7_700_000 + u64::from(width)));
        let case = |value: u32| {
            Proposition::condition_is(
                ConditionTerm::equal(x.clone(), MachineTerm::constant(value)),
                true,
            )
        };
        let disjunction = (0..width - 1).rev().fold(case(width - 1), |rest, value| {
            Proposition::Or(Box::new(case(value)), Box::new(rest))
        });
        let assumptions = PureFactContext::new().assume_proposition(disjunction);
        let nonnegative = Proposition::condition_is(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), x.clone()),
            true,
        );
        assert!(!crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &nonnegative
        ));
        assert_checkable_derivation(&assumptions, &nonnegative);
    }
}

/// The discharge rule shared by `add_required_proof_obligation_with_context`
/// and the call-requirement sites in `prepare_verified_function_call`.
///
/// Direct obligation checking follows AND/OR structure, but does not use
/// implication elimination or general proof search.
#[test]
fn required_obligation_discharge_uses_goal_connectives_without_search() {
    let value = MachineTerm::Variable(Variable(97_100));
    let positive = Proposition::condition_is(
        ConditionTerm::signed_less_than(MachineTerm::constant(0), value.clone()),
        true,
    );
    let nonnegative = Proposition::condition_is(
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), value.clone()),
        true,
    );
    let other = Proposition::condition_is(
        ConditionTerm::signed_less_than(
            MachineTerm::constant(0),
            MachineTerm::Variable(Variable(97_101)),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(positive.clone());

    // Exactly available, and the frozen condition checker's own consequence.
    assert!(required_obligation_is_exactly_discharged(
        &assumptions,
        &positive
    ));
    assert!(required_obligation_is_exactly_discharged(
        &assumptions,
        &nonnegative
    ));

    // A known arm settles OR, including within AND. Missing conjuncts and
    // implication search remain outside this direct rule.
    let disjunction = Proposition::Or(Box::new(positive.clone()), Box::new(other.clone()));
    assert!(required_obligation_is_exactly_discharged(
        &assumptions,
        &disjunction
    ));
    let conjunction = Proposition::And(Box::new(disjunction.clone()), Box::new(positive.clone()));
    assert!(required_obligation_is_exactly_discharged(
        &assumptions,
        &conjunction
    ));
    let missing = Proposition::And(Box::new(positive.clone()), Box::new(other.clone()));
    assert!(!required_obligation_is_exactly_discharged(
        &assumptions,
        &missing
    ));
    let held_or = PureFactContext::new().assume_proposition(disjunction.clone());
    assert!(required_obligation_is_exactly_discharged(
        &held_or,
        &disjunction
    ));
    assert!(!required_obligation_is_exactly_discharged(
        &held_or, &positive
    ));
    assert!(!required_obligation_is_exactly_discharged(
        &PureFactContext::new(),
        &disjunction
    ));
    let implication = Proposition::Implies(Box::new(other.clone()), Box::new(nonnegative.clone()));
    assert!(!required_obligation_is_exactly_discharged(
        &assumptions,
        &implication
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &disjunction
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &implication
    ));

    // And the emitted obligation is the required (non-assumable) kind,
    // carrying its context.
    let mut obligations = Vec::new();
    add_required_proof_obligation_with_context(
        &mut obligations,
        &assumptions,
        missing.clone(),
        Some("callee precondition"),
        None,
    );
    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].proposition(), &missing);
    assert!(!obligations[0].is_assumable());
    assert_eq!(obligations[0].context(), Some("callee precondition"));
}

#[test]
fn range_fold_alpha_identity_separates_a_bound_accumulator_from_a_free_variable() {
    // `left` returns its initial value; `right` returns the free `shared`
    // whenever its range is non-empty. The two folds denote different values,
    // and the only thing that could make them look alike is that `shared` is
    // the name `left` binds as its accumulator.
    let shared = Variable(152);
    let item = Variable(153);
    let right_accumulator = Variable(154);
    let start = MachineTerm::Variable(Variable(150));
    let end = MachineTerm::Variable(Variable(151));

    let left = MachineTerm::range_fold(
        start.clone(),
        end.clone(),
        MachineTerm::constant(0),
        shared,
        item,
        MachineTerm::Variable(shared),
    );
    let right = MachineTerm::range_fold(
        start,
        end,
        MachineTerm::constant(0),
        right_accumulator,
        item,
        MachineTerm::Variable(shared),
    );

    let assumptions = PureFactContext::new();
    assert!(
        !assumptions.range_fold_terms_alpha_equivalent(&left, &right),
        "a bound accumulator occurrence must not match a free variable of the same id"
    );
    assert!(!assumptions.bitvector_terms_proven_equal(&left, &right));
    // Contract certification asks the same question of the same identity.
    assert_eq!(
        crate::kernel::proof::fact_keys::bitvector_folds_alpha_equivalent(&left, &right),
        Some(false)
    );
}

/// A fold whose body rebinds the enclosing accumulator's name against one
/// whose body reads it. This is the shape `mdtests/
/// fold_binder_is_not_an_enclosing_accumulator.md` writes in Click: fold
/// binder ids are hashed from the binder's name, so two `|acc, ..|` folds bind
/// one id and an inner `|acc, ..|` shadows an outer one.
#[test]
fn a_shadowing_fold_binder_differs_from_a_read_of_the_enclosing_accumulator() {
    let outer_accumulator = Variable(160);
    let outer_item = Variable(161);
    let inner_item = Variable(162);
    let inner_accumulator = Variable(163);
    let start = MachineTerm::Variable(Variable(164));
    let end = MachineTerm::Variable(Variable(165));

    let nest = |inner_accumulator, inner_body| {
        MachineTerm::range_fold(
            start.clone(),
            end.clone(),
            MachineTerm::constant(0),
            outer_accumulator,
            outer_item,
            MachineTerm::add(
                MachineTerm::range_fold(
                    start.clone(),
                    end.clone(),
                    MachineTerm::constant(0),
                    inner_accumulator,
                    inner_item,
                    inner_body,
                ),
                MachineTerm::constant(1),
            ),
        )
    };

    // The inner fold rebinds `outer_accumulator`, so its body reads its own
    // accumulator and it returns its initial value.
    let shadowing = nest(outer_accumulator, MachineTerm::Variable(outer_accumulator));
    // The inner fold binds a different name, so the same body reads the
    // enclosing accumulator.
    let reading = nest(inner_accumulator, MachineTerm::Variable(outer_accumulator));

    let assumptions = PureFactContext::new();
    assert!(!assumptions.range_fold_terms_alpha_equivalent(&shadowing, &reading));
    assert!(!assumptions.bitvector_terms_proven_equal(&shadowing, &reading));

    // Renaming every binder of either one keeps it equal to itself: the
    // distinction above is about binding, not about spelling.
    let renamed_shadowing = MachineTerm::range_fold(
        start.clone(),
        end.clone(),
        MachineTerm::constant(0),
        Variable(170),
        Variable(171),
        MachineTerm::add(
            MachineTerm::range_fold(
                start.clone(),
                end.clone(),
                MachineTerm::constant(0),
                Variable(172),
                Variable(173),
                MachineTerm::Variable(Variable(172)),
            ),
            MachineTerm::constant(1),
        ),
    );
    assert!(assumptions.range_fold_terms_alpha_equivalent(&shadowing, &renamed_shadowing));

    let renamed_reading = MachineTerm::range_fold(
        start,
        end,
        MachineTerm::constant(0),
        Variable(180),
        Variable(181),
        MachineTerm::add(
            MachineTerm::range_fold(
                MachineTerm::Variable(Variable(164)),
                MachineTerm::Variable(Variable(165)),
                MachineTerm::constant(0),
                Variable(182),
                Variable(183),
                MachineTerm::Variable(Variable(180)),
            ),
            MachineTerm::constant(1),
        ),
    );
    assert!(assumptions.range_fold_terms_alpha_equivalent(&reading, &renamed_reading));
    assert!(!assumptions.range_fold_terms_alpha_equivalent(&shadowing, &renamed_reading));
}

#[test]
fn range_fold_alpha_identity_keeps_renamed_binders_and_shared_free_variables_equal() {
    let free = Variable(190);
    let start = MachineTerm::Variable(Variable(191));
    let end = MachineTerm::Variable(Variable(192));

    // `acc + item + free`, under two disjoint sets of binder names.
    let summed = |accumulator, item| {
        MachineTerm::range_fold(
            start.clone(),
            end.clone(),
            MachineTerm::constant(0),
            accumulator,
            item,
            MachineTerm::add(
                MachineTerm::add(
                    MachineTerm::Variable(accumulator),
                    MachineTerm::Variable(item),
                ),
                MachineTerm::Variable(free),
            ),
        )
    };
    let left = summed(Variable(193), Variable(194));
    let right = summed(Variable(195), Variable(196));

    let assumptions = PureFactContext::new();
    assert!(assumptions.range_fold_terms_alpha_equivalent(&left, &right));
    assert!(assumptions.bitvector_terms_proven_equal(&left, &right));
    assert_eq!(
        crate::kernel::proof::fact_keys::bitvector_folds_alpha_equivalent(&left, &right),
        Some(true)
    );

    // A different free variable in the same position is a different fold.
    let other_free = summed(Variable(193), Variable(194));
    let other_free = crate::kernel::reasoning::substitute_bitvector_variable(
        &other_free,
        free,
        &MachineTerm::Variable(Variable(197)),
    );
    assert!(!assumptions.range_fold_terms_alpha_equivalent(&left, &other_free));
}

#[test]
fn range_fold_alpha_identity_equates_nested_folds_under_renamed_binders() {
    let start = MachineTerm::Variable(Variable(200));
    let end = MachineTerm::Variable(Variable(201));

    // `fold(|acc, k| acc + fold(|total, j| total + k))`: the inner body reads
    // the enclosing item binder, so the two nestings only match when that
    // outer binder is aligned as well.
    let nested = |accumulator, item, inner_accumulator, inner_item| {
        MachineTerm::range_fold(
            start.clone(),
            end.clone(),
            MachineTerm::constant(0),
            accumulator,
            item,
            MachineTerm::add(
                MachineTerm::Variable(accumulator),
                MachineTerm::range_fold(
                    start.clone(),
                    end.clone(),
                    MachineTerm::constant(0),
                    inner_accumulator,
                    inner_item,
                    MachineTerm::add(
                        MachineTerm::Variable(inner_accumulator),
                        MachineTerm::Variable(item),
                    ),
                ),
            ),
        )
    };
    let left = nested(Variable(202), Variable(203), Variable(204), Variable(205));
    let right = nested(Variable(206), Variable(207), Variable(208), Variable(209));

    let assumptions = PureFactContext::new();
    assert!(assumptions.range_fold_terms_alpha_equivalent(&left, &right));
    assert!(assumptions.bitvector_terms_proven_equal(&left, &right));

    // Reading the inner item binder instead of the outer one is a different
    // fold, and renaming cannot hide that either.
    let inner_item_instead = MachineTerm::range_fold(
        start.clone(),
        end.clone(),
        MachineTerm::constant(0),
        Variable(206),
        Variable(207),
        MachineTerm::add(
            MachineTerm::Variable(Variable(206)),
            MachineTerm::range_fold(
                start,
                end,
                MachineTerm::constant(0),
                Variable(208),
                Variable(209),
                MachineTerm::add(
                    MachineTerm::Variable(Variable(208)),
                    MachineTerm::Variable(Variable(209)),
                ),
            ),
        ),
    );
    assert!(!assumptions.range_fold_terms_alpha_equivalent(&left, &inner_item_instead));
}

/// A lower-bound search compares its term with the ambient order facts at
/// most once, at the outermost search; the searches its recursive `decide`
/// calls start read only the bounds recorded at their own term
/// (`signed_order_bounds`). It used to rescan every fact at every level of
/// the recursion, so its work was the fact count to the power of the chain
/// depth; in `examples/arena`'s pipeline one loadability check spent 96
/// seconds there.
#[test]
fn lower_bound_search_ignores_unrelated_facts() {
    let bounded = MachineTerm::Variable(Variable(97_500));
    let middle = MachineTerm::Variable(Variable(97_501));
    let inner = MachineTerm::Variable(Variable(97_502));
    let zero = MachineTerm::constant(0);
    let samples = [16, 64, 256]
        .into_iter()
        .map(|size| {
            // `bounded >= middle >= inner >= 1`: the searches must recurse
            // through `middle` and `inner` to reach the constant.
            let mut assumptions = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_greater_equal(bounded.clone(), middle.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_greater_equal(middle.clone(), inner.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_greater_equal(inner.clone(), MachineTerm::constant(1)),
                    true,
                );
            for index in 0..size {
                let unrelated = MachineTerm::Variable(Variable(97_600 + index as u64));
                assumptions = assumptions
                    .assume_condition(
                        ConditionTerm::signed_greater_equal(unrelated.clone(), zero.clone()),
                        true,
                    )
                    .assume_condition(
                        ConditionTerm::signed_less_equal(unrelated, MachineTerm::constant(1_000)),
                        true,
                    );
            }
            PureFactContext::reset_lower_bound_candidate_visits();
            let found = assumptions.has_lower_bound_at_or_above(&bounded, &zero)
                && assumptions.has_lower_bound_above(&bounded, &zero);
            assert!(found, "size {size}: the recorded chain was not found");
            let facts = assumptions.condition_facts.len();
            (facts, PureFactContext::lower_bound_candidate_visits())
        })
        .collect::<Vec<_>>();
    // Two searches, each scanning the order facts once at its outermost level
    // and reading only indexed entries below it.
    assert!(
        samples
            .iter()
            .all(|(facts, visits)| *visits <= 2 * facts + 16),
        "a nested lower-bound search rescanned the fact set: {samples:?}"
    );
}

#[test]
fn direct_constant_index_requires_written_premises_and_preserves_forks() {
    let a = MachineTerm::Variable(Variable(97_010));
    let b = MachineTerm::Variable(Variable(97_011));
    let edge = ConditionTerm::equal(a.clone(), b.clone());
    let context = PureFactContext::new()
        .assume_condition(edge.clone(), true)
        .assume_condition(ConditionTerm::equal(b.clone(), 7u32.into()), true);
    assert_eq!(context.bitvector_constant_from_direct_equalities(&a), None);
    assert_eq!(
        context.bitvector_constant_from_direct_equalities(&b),
        Some(7)
    );
    let pin = ConditionTerm::equal(a.clone(), 7u32.into());
    let explicit = context.clone().assume_condition(pin.clone(), true);
    assert_eq!(
        explicit.bitvector_constant_from_direct_equalities(&a),
        Some(7)
    );
    assert_eq!(context.bitvector_constant_from_direct_equalities(&a), None);
    let restricted = explicit.restricted_to_facts(&[(edge, true)], &[]);
    assert_eq!(
        restricted.bitvector_constant_from_direct_equalities(&a),
        None
    );
    let contradictory = explicit.clone().assume_condition(pin, false);
    assert!(contradictory.is_inconsistent());
    // Opposite assumptions do not withdraw the original written premise.
    assert_eq!(
        contradictory.bitvector_constant_from_direct_equalities(&a),
        Some(7)
    );
    let compound = MachineTerm::add(a.clone(), 1u32.into());
    assert_eq!(
        explicit.bitvector_constant_from_direct_equalities(&compound),
        None
    );
    let with_compound = explicit
        .clone()
        .assume_condition(ConditionTerm::equal(compound.clone(), 8u32.into()), true);
    assert_eq!(
        with_compound.bitvector_constant_from_direct_equalities(&compound),
        Some(8)
    );
    let wide = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_equal(a.clone(), MachineTerm::uint64_constant(7)),
        true,
    );
    assert_eq!(wide.bitvector_constant_from_direct_equalities(&a), None);
    let conflicting = explicit
        .clone()
        .assume_condition(ConditionTerm::equal(a.clone(), 9u32.into()), true);
    assert_eq!(
        conflicting.bitvector_constant_from_direct_equalities(&a),
        None
    );
    assert_eq!(
        explicit.bitvector_constant_from_direct_equalities(&a),
        Some(7)
    );
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
        for (left, right) in [
            (a.clone(), 0xffff_ffffu32.into()),
            (0xffff_ffffu32.into(), a.clone()),
        ] {
            let fact = ConditionTerm::Compare {
                format,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            };
            let facts = PureFactContext::new().assume_condition(fact, true);
            assert_eq!(
                facts.bitvector_constant_from_direct_equalities(&a),
                Some(u32::MAX)
            );
        }
    }
}

/// Constant normalization keeps its decisions when its classes are built
/// incrementally: a counter chain resolves whatever order its facts arrive
/// in, a second constant anywhere in a class makes that class ambiguous (and
/// only that class), and withdrawing or replacing the conflicting fact
/// restores the unique constant.
#[test]
fn constant_normalization_classes_detect_ambiguity_in_any_insertion_order() {
    let counter = |index: u64| MachineTerm::Variable(Variable(930_200 + index));
    let successor = |index: u64| {
        ConditionTerm::equal(
            counter(index + 1),
            MachineTerm::add(counter(index), 1u32.into()),
        )
    };
    let start = ConditionTerm::equal(counter(0), MachineTerm::constant(0));
    // The chain's facts arrive last-first, so every constant reaches the
    // later counters only by propagation through the recorded sums.
    let mut chain = PureFactContext::new();
    for index in (0..4).rev() {
        chain = chain.assume_condition(successor(index), true);
    }
    assert_eq!(
        chain.known_signed_constant_after_normalization(&counter(4)),
        None
    );
    let chain = chain.assume_condition(start, true);
    for index in 0..=4 {
        assert_eq!(
            chain.known_signed_constant_after_normalization(&counter(index)),
            Some(index as i64),
        );
    }

    let conflict = ConditionTerm::equal(counter(2), MachineTerm::constant(7));
    let ambiguous = chain.assume_condition(conflict.clone(), true);
    for index in 2..=4 {
        assert_eq!(
            ambiguous.known_signed_constant_after_normalization(&counter(index)),
            None,
            "counter {index} is 2 through the chain and 7 through the conflict"
        );
    }
    for index in 0..=1 {
        assert_eq!(
            ambiguous.known_signed_constant_after_normalization(&counter(index)),
            Some(index as i64),
            "the conflict does not reach counter {index}, which only feeds it"
        );
    }
    // Joining an ambiguous class to another term makes that term ambiguous.
    let alias = MachineTerm::Variable(Variable(930_299));
    let joined = ambiguous
        .clone()
        .assume_condition(ConditionTerm::equal(alias.clone(), counter(4)), true);
    assert_eq!(
        joined.known_signed_constant_after_normalization(&alias),
        None
    );

    let replaced = ambiguous.clone().assume_condition(conflict, false);
    assert!(replaced.is_inconsistent());
    assert_eq!(
        replaced.known_signed_constant_after_normalization(&counter(4)),
        None,
        "opposite assumptions do not erase the conflicting constant"
    );
}

#[test]
fn reflexive_comparisons_decide_without_facts_and_strict_ones_are_false() {
    let n = MachineTerm::Variable(Variable(89_200));
    let m = MachineTerm::Variable(Variable(89_201));
    let empty = PureFactContext::new();
    let cases = [
        (ConditionTerm::signed_less_equal(n.clone(), n.clone()), true),
        (
            ConditionTerm::signed_greater_equal(n.clone(), n.clone()),
            true,
        ),
        (ConditionTerm::equal(n.clone(), n.clone()), true),
        (ConditionTerm::signed_less_than(n.clone(), n.clone()), false),
        (
            ConditionTerm::signed_greater_than(n.clone(), n.clone()),
            false,
        ),
    ];
    for (condition, value) in cases {
        assert_eq!(condition.reflexive_value(), Some(value), "{condition:?}");
        assert_eq!(empty.decide(&condition), Some(value), "{condition:?}");
        assert!(crate::kernel::proposition_holds_without_facts(
            &Proposition::condition_is(condition.clone(), value)
        ));
        assert!(!crate::kernel::proposition_holds_without_facts(
            &Proposition::condition_is(condition, !value)
        ));
    }
    // Distinct operands are not reflexive: nothing is decided without facts.
    let distinct = ConditionTerm::signed_less_equal(n, m);
    assert_eq!(distinct.reflexive_value(), None);
    assert_eq!(empty.decide(&distinct), None);
    assert!(!crate::kernel::proposition_holds_without_facts(
        &Proposition::condition_is(distinct, true)
    ));
}

/// The condition checker (`decide`) and the memory-resolution order prover
/// answer every successor and int32-extreme comparison against `x < y` the
/// same way. Each row names the comparison and whether it follows from
/// `0 <= x` and `x < y` for every int32 `x` and `y`; the rows that do not
/// follow (`x + 1` may reach `y`, or `y + 1` / `x + 2` may wrap) are refused
/// by both.
#[test]
fn signed_order_provers_agree_on_successor_terms() {
    let x = MachineTerm::Variable(Variable(89_300));
    let y = MachineTerm::Variable(Variable(89_301));
    let plus = |t: &MachineTerm, c: u32| {
        binary_node!(
            Int32,
            Add,
            Box::new(t.clone()),
            Box::new(MachineTerm::constant(c))
        )
    };
    let constant = |value: i32| MachineTerm::constant(value as u32);
    let facts = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(x.clone(), y.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_equal(constant(0), x.clone()),
            true,
        );
    let lt = ConditionTerm::signed_less_than;
    let le = ConditionTerm::signed_less_equal;
    let gt = ConditionTerm::signed_greater_than;
    let ge = ConditionTerm::signed_greater_equal;
    let cases = [
        ("x < x + 1", lt(x.clone(), plus(&x, 1)), true),
        ("x <= x + 1", le(x.clone(), plus(&x, 1)), true),
        ("x + 1 > x", gt(plus(&x, 1), x.clone()), true),
        ("x + 1 >= x", ge(plus(&x, 1), x.clone()), true),
        ("x + 1 <= y", le(plus(&x, 1), y.clone()), true),
        ("y >= x + 1", ge(y.clone(), plus(&x, 1)), true),
        ("y > x", gt(y.clone(), x.clone()), true),
        ("y >= x", ge(y.clone(), x.clone()), true),
        ("x < INT32_MAX", lt(x.clone(), constant(i32::MAX)), true),
        ("INT32_MAX > x", gt(constant(i32::MAX), x.clone()), true),
        ("x <= INT32_MAX", le(x.clone(), constant(i32::MAX)), true),
        (
            "x + 1 <= INT32_MAX",
            le(plus(&x, 1), constant(i32::MAX)),
            true,
        ),
        ("0 <= x + 1", le(constant(0), plus(&x, 1)), true),
        ("0 < x + 1", lt(constant(0), plus(&x, 1)), true),
        ("1 <= x + 1", le(constant(1), plus(&x, 1)), true),
        ("x + 1 >= 1", ge(plus(&x, 1), constant(1)), true),
        ("x + 1 < y", lt(plus(&x, 1), y.clone()), false),
        ("x + 2 <= y", le(plus(&x, 2), y.clone()), false),
        ("x < x + 2", lt(x.clone(), plus(&x, 2)), false),
        ("x < y + 1", lt(x.clone(), plus(&y, 1)), false),
    ];
    for (name, condition, follows) in cases {
        let decided = facts.decide(&condition) == Some(true);
        let resolved = facts.proves_order_condition_for_memory_resolution(&condition, true);
        assert_eq!(decided, follows, "condition checker on `{name}`");
        assert_eq!(resolved, follows, "memory-resolution prover on `{name}`");
    }
}

#[test]
fn invalid_unsigned_constant_operations_do_not_panic() {
    for term in [
        MachineTerm::uint64_divide(
            MachineTerm::uint64_constant(1),
            MachineTerm::uint64_constant(0),
        ),
        MachineTerm::uint64_remainder(
            MachineTerm::uint64_constant(1),
            MachineTerm::uint64_constant(0),
        ),
        MachineTerm::uint64_logical_shift_right(
            MachineTerm::uint64_constant(1),
            MachineTerm::constant(64),
        ),
    ] {
        assert_eq!(term.uint64_as_const(), None);
    }
    assert_eq!(
        MachineTerm::unsigned_divide(MachineTerm::constant(1), MachineTerm::constant(0)).as_const(),
        None
    );
    assert_eq!(
        MachineTerm::unsigned_remainder(MachineTerm::constant(1), MachineTerm::constant(0))
            .as_const(),
        None
    );
}

#[test]
fn wide_scaled_offset_congruence_checks_full_width_and_scale() {
    let index = MachineTerm::Variable(Variable(992_000));
    let sum = MachineTerm::uint64_add(index.clone(), MachineTerm::uint64_constant(1));
    let offset = AddressOffset::scale_int64(sum, 4, true);
    let zero = PureFactContext::new().assume_proposition(Proposition::condition_is(
        ConditionTerm::uint64_equal(index.clone(), MachineTerm::uint64_constant(0)),
        true,
    ));
    let four = AddressOffset::Constant(4);
    let evidence = zero
        .pointer_offset_congruence_evidence(&offset, &four)
        .unwrap();
    assert!(evidence.checks(&offset, &four, &zero));
    assert!(!evidence.checks(&offset, &AddressOffset::Constant(0), &zero));
    assert!(!evidence.checks(&offset, &four, &PureFactContext::new()));
    let high = PureFactContext::new().assume_proposition(Proposition::condition_is(
        ConditionTerm::uint64_equal(index.clone(), MachineTerm::uint64_constant(4294967296)),
        true,
    ));
    assert!(!evidence.checks(&offset, &four, &high));
    let low_word_only = PureFactContext::new().assume_proposition(Proposition::condition_is(
        ConditionTerm::equal(index, MachineTerm::constant(0)),
        true,
    ));
    assert!(!evidence.checks(&offset, &four, &low_word_only));
    let overflowing =
        AddressOffset::scaled_int64_node(MachineTerm::uint64_constant(i64::MAX as u64), 2, true);
    assert!(
        zero.pointer_offset_congruence_evidence(&overflowing, &AddressOffset::Constant(-2))
            .is_none()
    );
}

/// Each uint32 order axiom holds at every boundary value: the kernel's own
/// evaluation of its premise and conclusion over constants never finds the
/// premise true and the conclusion false. The values straddle zero, the sign
/// bit the unsigned order is encoded through, and `UINT_MAX`, where an
/// increment or a decrement wraps.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn uint32_order_axioms_hold_at_the_wrapping_boundaries() {
    const BOUNDARIES: [u32; 9] = [
        0,
        1,
        2,
        0x7fff_ffff,
        0x8000_0000,
        0x8000_0001,
        0xffff_fffd,
        0xffff_fffe,
        0xffff_ffff,
    ];
    fn holds(theorem: &Theorem) -> bool {
        let decide = |proposition: &Proposition| {
            let Proposition::ConditionIs(condition, true) = proposition else {
                panic!("a uint32 order axiom relates conditions");
            };
            PureFactContext::decide_intrinsically(condition.native_compat())
                .expect("a condition over constants is decided")
        };
        // One premise, or two for a transitivity, then the conclusion.
        let mut proposition = theorem.proposition();
        let mut premises = 0usize;
        while let Proposition::Implies(premise, rest) = proposition {
            if !decide(premise) {
                return true;
            }
            premises += 1;
            proposition = rest;
        }
        assert!(premises > 0, "a uint32 order axiom has a premise");
        decide(proposition)
    }
    let constant = MachineTerm::constant;
    let mut premises_true = 0usize;
    for left in BOUNDARIES {
        for right in BOUNDARIES {
            let pair: [(&str, Theorem); 2] = [
                (
                    "lt reversed",
                    prove_uint32_lt_implies_reversed_gt(constant(left), constant(right)),
                ),
                (
                    "ge reversed",
                    prove_uint32_ge_implies_reversed_le(constant(left), constant(right)),
                ),
            ];
            for last in BOUNDARIES {
                assert!(
                    holds(&prove_uint32_le_lt_transitive(
                        constant(left),
                        constant(right),
                        constant(last)
                    )),
                    "transitivity at {left:#x}, {right:#x}, {last:#x}"
                );
            }
            for (name, theorem) in &pair {
                assert!(holds(theorem), "{name} at {left:#x}, {right:#x}");
            }
            if left < right {
                premises_true += 1;
            }
        }
    }
    // The strict-order premises are exercised, not only vacuous cases.
    assert_eq!(premises_true, 36);

    // Near-equal pairs, where a bound is tight, and a spread of ordinary
    // values from a fixed linear congruential sequence.
    let mut state = 0x2545_f491u32;
    let mut sampled = Vec::new();
    for _ in 0..4096 {
        state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        let left = state;
        state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        sampled.push((left, state));
        for delta in [0u32, 1, 2, u32::MAX, u32::MAX - 1] {
            sampled.push((left, left.wrapping_add(delta)));
        }
    }
    for left in BOUNDARIES {
        for delta in [0u32, 1, 2, u32::MAX, u32::MAX - 1] {
            sampled.push((left, left.wrapping_add(delta)));
        }
    }
    for (left, right) in sampled {
        for theorem in [
            prove_uint32_lt_implies_reversed_gt(constant(left), constant(right)),
            prove_uint32_ge_implies_reversed_le(constant(left), constant(right)),
            prove_uint32_le_lt_transitive(
                constant(left),
                constant(right),
                constant(right.wrapping_add(1)),
            ),
        ] {
            assert!(
                holds(&theorem),
                "{:?} at {left:#x}, {right:#x}",
                theorem.proposition()
            );
        }
    }

    // The check can fail: each conclusion is false where its premise is,
    // so a statement without its premise would not pass.
    let conclusion_holds = |theorem: &Theorem| {
        let mut conclusion = theorem.proposition();
        while let Proposition::Implies(_, rest) = conclusion {
            conclusion = rest;
        }
        let Proposition::ConditionIs(condition, true) = conclusion else {
            panic!("a uint32 order axiom relates conditions");
        };
        PureFactContext::decide_intrinsically(condition.native_compat())
            .expect("a condition over constants is decided")
    };
    assert!(!conclusion_holds(&prove_uint32_le_lt_transitive(
        constant(9),
        constant(3),
        constant(5)
    )));
}

#[test]
fn singleton_bound_through_an_exact_constant_equality_retains_its_premises() {
    let i = MachineTerm::Variable(Variable(9_890_001));
    let n = MachineTerm::Variable(Variable(9_890_002));
    let lower = Proposition::condition_is(
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), i.clone()),
        true,
    );
    let upper =
        Proposition::condition_is(ConditionTerm::signed_less_equal(i.clone(), n.clone()), true);
    let pinned = Proposition::condition_is(
        ConditionTerm::equal(n.clone(), MachineTerm::constant(0)),
        true,
    );
    let goal = Proposition::condition_is(ConditionTerm::equal(i, n), true);
    let facts = PureFactContext::new()
        .assume_proposition(lower.clone())
        .assume_proposition(upper.clone())
        .assume_proposition(pinned.clone());
    let proof = crate::kernel::search::ProofSearch::derive_solve_proposition(&(facts), &goal)
        .expect("typed singleton equality");
    assert!(proof.check(&facts));
    assert!(proof.is_int32_pinned_constant_equality());
    assert_eq!(
        proof
            .context_premises()
            .into_iter()
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([lower.clone(), upper.clone(), pinned.clone()])
    );
    let premises = [lower, upper, pinned];
    for missing in &premises {
        let restricted = premises
            .iter()
            .filter(|premise| *premise != missing)
            .cloned()
            .fold(PureFactContext::new(), PureFactContext::assume_proposition);
        assert!(!proof.check(&restricted));
        assert!(
            crate::kernel::search::ProofSearch::derive_solve_proposition(&(restricted), &goal)
                .is_none()
        );
    }
}

#[test]
fn int32_remainder_bridge_matches_independent_signed_boundary_models() {
    let left = MachineTerm::Variable(Variable(940));
    let right = MachineTerm::Variable(Variable(941));
    let theorem = prove_int32_remainder_to_integer(left.clone(), right.clone());
    let Proposition::Implies(native_defined, rest) = theorem.proposition() else {
        panic!("missing native definedness");
    };
    let Proposition::And(nonzero, no_overflow) = native_defined.as_ref() else {
        panic!("definedness must exclude both zero and overflow");
    };
    assert_eq!(
        nonzero.as_ref(),
        &Proposition::condition_is(
            ConditionTerm::equal(right.clone(), MachineTerm::constant(0)),
            false
        )
    );
    assert_eq!(
        no_overflow.as_ref(),
        &Proposition::signed_division_exclusion(MachineIntegerType::Int32, &left, &right)
    );
    let Proposition::Implies(integer_nonzero, conclusion) = rest.as_ref() else {
        panic!("missing mathematical domain");
    };
    let observe = |term| IntegerTerm::from_machine(MachineIntegerType::Int32, term).unwrap();
    assert_eq!(
        integer_nonzero.as_ref(),
        &Proposition::condition_is(
            ConditionTerm::integer_not_equal(observe(right.clone()), IntegerTerm::constant_i64(0)),
            true
        )
    );
    assert_eq!(
        conclusion.as_ref(),
        &Proposition::condition_is(
            ConditionTerm::IntegerEqual(
                observe(binary_node!(
                    Int32,
                    Remainder,
                    left.clone().into(),
                    right.clone().into()
                ))
                .into(),
                IntegerTerm::truncating_remainder(observe(left), observe(right)).into(),
            ),
            true
        )
    );
    for a in [
        i32::MIN,
        i32::MIN + 1,
        -22207,
        -5551,
        -4,
        -1,
        0,
        1,
        4,
        5551,
        22207,
        i32::MAX,
    ] {
        for b in [i32::MIN, -5551, -4, -1, 0, 1, 4, 5551, i32::MAX] {
            let defined = b != 0 && !(a == i32::MIN && b == -1);
            assert_eq!(a.checked_rem(b).is_some(), defined, "{a} % {b}");
            if let Some(remainder) = a.checked_rem(b) {
                let mathematical = num_bigint::BigInt::from(a) % num_bigint::BigInt::from(b);
                assert_eq!(
                    num_bigint::BigInt::from(remainder),
                    mathematical,
                    "{a} % {b}"
                );
            }
        }
    }
}

#[test]
fn uint32_division_integer_bridges_match_unsigned_boundary_models() {
    use num_bigint::BigInt;
    fn integer(term: &IntegerTerm) -> BigInt {
        match term {
            IntegerTerm::Constant(value) => value.clone(),
            IntegerTerm::Machine(value) => {
                assert_eq!(value.ty(), MachineIntegerType::UInt32);
                BigInt::from(value.value().as_const().expect("constant unsigned word"))
            }
            IntegerTerm::TruncatingQuotient(a, b) => integer(a) / integer(b),
            IntegerTerm::TruncatingRemainder(a, b) => integer(a) % integer(b),
            _ => panic!("unexpected observation"),
        }
    }
    for remainder in [false, true] {
        for value in [0, 1, 2, 65520, 65521, 1 << 31, u32::MAX - 1, u32::MAX] {
            for divisor in [0, 1, 2, 65521, 1 << 31, u32::MAX] {
                let theorem = if remainder {
                    prove_uint32_remainder_to_integer(
                        MachineTerm::constant(value),
                        MachineTerm::constant(divisor),
                    )
                } else {
                    prove_uint32_divide_to_integer(
                        MachineTerm::constant(value),
                        MachineTerm::constant(divisor),
                    )
                };
                let Proposition::Implies(native_guard, rest) = theorem.proposition() else {
                    panic!("native guard missing");
                };
                assert_eq!(
                    PureFactContext::new().proves_exact(native_guard),
                    divisor != 0
                );
                if divisor == 0 {
                    continue;
                }
                let Proposition::Implies(integer_guard, conclusion) = rest.as_ref() else {
                    panic!("Integer guard missing");
                };
                assert!(PureFactContext::new().proves_exact(integer_guard));
                let Some((ConditionTerm::IntegerEqual(a, b), true)) =
                    conclusion.as_ref().condition_native()
                else {
                    panic!("observation equality missing");
                };
                let expected = BigInt::from(if remainder {
                    value % divisor
                } else {
                    value / divisor
                });
                assert_eq!(integer(a), expected);
                assert_eq!(integer(b), expected);
            }
        }
    }
}

#[test]
fn uint64_integer_bridges_match_full_width_wrap_and_division_boundary_models() {
    use num_bigint::BigInt;
    fn integer(term: &IntegerTerm) -> BigInt {
        match term {
            IntegerTerm::Constant(value) => value.clone(),
            IntegerTerm::Machine(value) => {
                assert_eq!(value.ty(), MachineIntegerType::UInt64);
                BigInt::from(
                    value
                        .value()
                        .uint64_as_const()
                        .expect("constant unsigned operation"),
                )
            }
            IntegerTerm::Add(a, b) => integer(a) + integer(b),
            IntegerTerm::Subtract(a, b) => integer(a) - integer(b),
            IntegerTerm::Multiply(a, b) => integer(a) * integer(b),
            IntegerTerm::TruncatingQuotient(a, b) => integer(a) / integer(b),
            IntegerTerm::TruncatingRemainder(a, b) => integer(a) % integer(b),
            _ => panic!("unexpected observation term"),
        }
    }
    fn truth(proposition: &Proposition) -> bool {
        if let Proposition::And(a, b) = proposition {
            return truth(a) && truth(b);
        }
        let Proposition::ConditionIs(condition, expected) = proposition else {
            panic!("expected atomic relation");
        };
        let actual = match condition.native_compat() {
            ConditionTerm::Constant(value) => *value,
            ConditionTerm::IntegerNotEqual(a, b) => integer(a) != integer(b),
            ConditionTerm::IntegerLessEqual(a, b) => integer(a) <= integer(b),
            ConditionTerm::IntegerLessThan(a, b) => integer(a) < integer(b),
            ConditionTerm::IntegerEqual(a, b) => integer(a) == integer(b),
            _ => panic!("unexpected guard or equality"),
        };
        actual == *expected
    }
    for name in [
        "click::integer::uint64_divide_to_integer",
        "click::integer::uint64_remainder_to_integer",
    ] {
        for a in [
            0,
            1,
            2,
            (1 << 31) - 1,
            (1 << 33) - 1,
            1 << 63,
            u64::MAX - 1,
            u64::MAX,
        ] {
            for b in [
                0,
                1,
                2,
                (1 << 31) - 1,
                (1 << 33) - 1,
                1 << 63,
                u64::MAX - 1,
                u64::MAX,
            ] {
                let theorem = prove_uint64_integer_bridge(
                    name,
                    MachineTerm::uint64_constant(a),
                    MachineTerm::uint64_constant(b),
                )
                .unwrap();
                let Proposition::Implies(guard, conclusion) = theorem.proposition() else {
                    panic!("missing guard");
                };
                let allowed = b != 0;
                assert_eq!(truth(guard), allowed, "{name}/{a}/{b}");
                let conclusion =
                    if let Proposition::Implies(integer_guard, body) = conclusion.as_ref() {
                        assert_eq!(
                            truth(integer_guard),
                            allowed,
                            "{name}/{a}/{b} Integer domain"
                        );
                        body
                    } else {
                        conclusion
                    };
                if allowed {
                    assert!(truth(conclusion), "{name}/{a}/{b}");
                }
            }
        }
    }
    assert!(
        prove_uint64_integer_bridge(
            "uint64_unknown",
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(0)
        )
        .is_none()
    );
}

#[test]
fn mirrored_order_spellings_are_one_order_claim_in_every_order_family() {
    use crate::kernel::proof::fact_reasoning::{
        condition_polarity_equivalent, condition_polarity_forms, order_claim_equivalent,
        order_claim_forms,
    };
    let fact = |condition: ConditionTerm, value: bool| Proposition::condition_is(condition, value);

    // `0 <= e` and `e >= 0` over `Integer`, as a type-range bound fact
    // concludes the first and a goal may spell the second.
    let zero: SharedIntegerTerm = IntegerTerm::constant_i64(0).into();
    let observed: SharedIntegerTerm = IntegerTerm::var(Variable(93_000)).into();
    let lower_bound = fact(
        ConditionTerm::IntegerLessEqual(zero.clone(), observed.clone()),
        true,
    );
    let mirrored = fact(
        ConditionTerm::IntegerGreaterEqual(observed.clone(), zero.clone()),
        true,
    );
    assert!(order_claim_equivalent(&lower_bound, &mirrored));
    assert!(order_claim_equivalent(&mirrored, &lower_bound));
    assert!(order_claim_forms(&mirrored).contains(&lower_bound));
    // The availability paths and planners keep the 32-bit signed order only.
    assert!(!condition_polarity_equivalent(&lower_bound, &mirrored));
    assert!(!condition_polarity_forms(&mirrored).contains(&lower_bound));
    // `not (e < 0)` is the same claim again; a strict `0 < e` is not.
    let not_below = Proposition::Not(Box::new(fact(
        ConditionTerm::IntegerLessThan(observed.clone(), zero.clone()),
        true,
    )));
    assert!(order_claim_equivalent(&lower_bound, &not_below));
    let strictly_positive = fact(
        ConditionTerm::IntegerLessThan(zero.clone(), observed.clone()),
        true,
    );
    assert!(!order_claim_equivalent(&lower_bound, &strictly_positive));
    assert!(!order_claim_forms(&lower_bound).contains(&strictly_positive));
    // The strict claim has its own mirrored spelling.
    let strictly_positive_mirrored = fact(
        ConditionTerm::IntegerGreaterThan(observed.clone(), zero.clone()),
        true,
    );
    assert!(order_claim_equivalent(
        &strictly_positive,
        &strictly_positive_mirrored
    ));
    assert!(order_claim_forms(&strictly_positive).contains(&strictly_positive_mirrored));
    // Different sides are a different claim.
    let other: SharedIntegerTerm = IntegerTerm::var(Variable(93_001)).into();
    let other_bound = fact(
        ConditionTerm::IntegerGreaterEqual(other, zero.clone()),
        true,
    );
    assert!(!order_claim_equivalent(&lower_bound, &other_bound));

    // The 64-bit machine orders normalize the same way, and never across
    // families: a signed and an unsigned comparison of the same terms differ.
    let left = Box::new(MachineTerm::Variable(Variable(93_002)));
    let right = Box::new(MachineTerm::Variable(Variable(93_003)));
    let signed_below = fact(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::LessThan,
            left: left.clone(),
            right: right.clone(),
        },
        true,
    );
    let signed_above_mirrored = fact(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::GreaterThan,
            left: right.clone(),
            right: left.clone(),
        },
        true,
    );
    let signed_not_at_least = fact(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::GreaterEqual,
            left: left.clone(),
            right: right.clone(),
        },
        false,
    );
    assert!(order_claim_equivalent(
        &signed_below,
        &signed_above_mirrored
    ));
    assert!(order_claim_equivalent(&signed_below, &signed_not_at_least));
    assert!(order_claim_forms(&signed_below).contains(&signed_above_mirrored));
    assert!(!condition_polarity_equivalent(
        &signed_below,
        &signed_above_mirrored
    ));
    let unsigned_above_mirrored = fact(
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterThan,
            left: right.clone(),
            right: left.clone(),
        },
        true,
    );
    assert!(!order_claim_equivalent(
        &signed_below,
        &unsigned_above_mirrored
    ));
    let unsigned_below = fact(
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: left.clone(),
            right: right.clone(),
        },
        true,
    );
    assert!(order_claim_equivalent(
        &unsigned_below,
        &unsigned_above_mirrored
    ));

    // Over the 32-bit signed order both judgments agree, as before.
    let below = fact(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: left.clone(),
            right: right.clone(),
        },
        true,
    );
    let above_mirrored = fact(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left: right,
            right: left,
        },
        true,
    );
    assert!(condition_polarity_equivalent(&below, &above_mirrored));
    assert!(order_claim_equivalent(&below, &above_mirrored));
    assert_eq!(condition_polarity_forms(&below), order_claim_forms(&below));
}

#[test]
fn bounded_byte_pointer_association_uses_checked_signed_addition() {
    let i = MachineTerm::Variable(Variable(198001));
    let left = AddressOffset::Add(
        Box::new(AddressOffset::scale_int32(i.clone(), 1)),
        Box::new(AddressOffset::Constant(4)),
    );
    let right =
        AddressOffset::scale_int32(MachineTerm::add(i.clone(), MachineTerm::constant(4)), 1);
    let condition = ConditionTerm::address_offset_equal(left.clone(), right.clone());
    let goal = Proposition::condition_is(condition.clone(), true);
    let defined = Proposition::condition_is(
        ConditionTerm::signed_add_overflows(i.clone(), MachineTerm::constant(4)),
        false,
    );
    let facts = PureFactContext::new()
        .assume_proposition(Proposition::condition_is(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), i.clone()),
            true,
        ))
        .assume_proposition(Proposition::condition_is(
            ConditionTerm::signed_less_equal(i, MachineTerm::constant(22200)),
            true,
        ))
        .assume_proposition(defined.clone());
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            std::slice::from_ref(&defined),
            &crate::kernel::proof::PureFactStore::from_ordered(std::slice::from_ref(&defined)),
        )
        .is_ok()
    );
    assert_eq!(facts.decide(&condition), Some(true));
    assert!(
        crate::kernel::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
            &left, &right, &facts
        )
    );
    assert_eq!(
        facts
            .selected_for_test()
            .decide_selected_condition(&condition),
        Some(true)
    );
    let proof = crate::kernel::search::ProofSearch::derive_solve_proposition(&(facts), &goal)
        .expect("exact bounded pointer association");
    assert!(proof.check(&facts));
}

#[test]
fn pointer_association_rejects_wrapping_and_incompatible_displacements() {
    use crate::kernel::proof::term_rewrite::TermRewrite;
    use std::collections::HashMap;
    let i = MachineTerm::Variable(Variable(198101));
    let j = MachineTerm::Variable(Variable(198102));
    let overflow = ConditionTerm::signed_add_overflows(i.clone(), j.clone());
    for width in [1, 4, 8, i64::from(u32::MAX)] {
        let left = AddressOffset::Add(
            Box::new(AddressOffset::scale_int32(i.clone(), width)),
            Box::new(AddressOffset::scale_int32(j.clone(), width)),
        );
        let right = AddressOffset::scale_int32(MachineTerm::add(i.clone(), j.clone()), width);
        let condition = ConditionTerm::address_offset_equal(left.clone(), right.clone());
        let reversed = ConditionTerm::address_offset_equal(right, left.clone());
        let no_wrap = HashMap::from([(overflow.clone(), false)]);
        let base = AddressOffset::Variable(Variable(198103));
        let based_left = AddressOffset::Add(
            Box::new(AddressOffset::Add(
                Box::new(base.clone()),
                Box::new(AddressOffset::scale_int32(i.clone(), width)),
            )),
            Box::new(AddressOffset::scale_int32(j.clone(), width)),
        );
        let based_right = AddressOffset::Add(
            Box::new(base),
            Box::new(AddressOffset::scale_int32(
                MachineTerm::add(i.clone(), j.clone()),
                width,
            )),
        );
        let based = ConditionTerm::address_offset_equal(based_left.clone(), based_right);
        let different_base = ConditionTerm::address_offset_equal(
            based_left,
            AddressOffset::Add(
                Box::new(AddressOffset::Variable(Variable(198104))),
                Box::new(AddressOffset::scale_int32(
                    MachineTerm::add(i.clone(), j.clone()),
                    width,
                )),
            ),
        );
        assert_ne!(
            TermRewrite::for_conditions(&no_wrap).condition(&different_base),
            ConditionTerm::Constant(true)
        );
        for goal in [&condition, &reversed, &based] {
            assert_eq!(
                TermRewrite::for_conditions(&no_wrap).condition(goal),
                ConditionTerm::Constant(true)
            );
            assert_ne!(
                TermRewrite::for_conditions(&HashMap::new()).condition(goal),
                ConditionTerm::Constant(true)
            );
            assert_ne!(
                TermRewrite::for_conditions(&HashMap::from([(overflow.clone(), true)]))
                    .condition(goal),
                ConditionTerm::Constant(true)
            );
        }
        let wrong_stride = ConditionTerm::address_offset_equal(
            left.clone(),
            AddressOffset::scale_int32(MachineTerm::add(i.clone(), j.clone()), width + 1),
        );
        let wrong_index = ConditionTerm::address_offset_equal(
            left,
            AddressOffset::scale_int32(
                MachineTerm::add(i.clone(), MachineTerm::constant(5)),
                width,
            ),
        );
        for goal in [wrong_stride, wrong_index] {
            assert_ne!(
                TermRewrite::for_conditions(&no_wrap).condition(&goal),
                ConditionTerm::Constant(true)
            );
        }
    }
    // The exact byte sum differs from the wrapped signed scalar at the limit.
    let max = MachineTerm::constant(i32::MAX as u32);
    let exact = AddressOffset::Add(
        Box::new(AddressOffset::scale_int32(max.clone(), 1)),
        Box::new(AddressOffset::Constant(4)),
    );
    let wrapped = AddressOffset::scale_int32(MachineTerm::add(max, MachineTerm::constant(4)), 1);
    let false_goal = ConditionTerm::address_offset_equal(exact, wrapped);
    assert_ne!(
        TermRewrite::for_conditions(&HashMap::new()).condition(&false_goal),
        ConditionTerm::Constant(true)
    );
}

#[test]
fn native_loadability_transport_pins_span_domain_and_lifetime() {
    let base = Address {
        base: "native-region".into(),
        offset: AddressOffset::Constant(0),
    };
    let live = SymbolicMemory::new().with_block("native-region", 8);
    let fact = |memory: SymbolicMemory, bytes, wide| Proposition::MemoryLoadable {
        memory,
        base: base.clone(),
        bytes: crate::kernel::StoredMachineTerm::new(
            if wide {
                crate::kernel::MachineIntegerType::UInt64
            } else {
                crate::kernel::MachineIntegerType::Int32
            },
            bytes,
        ),
        wide,
    };
    let source = fact(live.clone(), MachineTerm::uint64_constant(8), true);
    let context = PureFactContext::new().assume_proposition(source.clone());
    let written = live
        .clone()
        .store(base.clone(), ProgramValue::Int32(MachineTerm::constant(7)));
    let goal = fact(written, MachineTerm::uint64_constant(8), true);
    let proof = crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
        .expect("writes preserve native liveness");
    assert!(proof.check(&context));
    assert_eq!(proof.context_premises(), vec![source]);
    for wrong in [
        fact(live.clone(), MachineTerm::uint64_constant(9), true),
        fact(
            live.clone().with_block("native-region", 2),
            MachineTerm::uint64_constant(8),
            true,
        ),
        fact(
            live.without_local_block(&base.base),
            MachineTerm::uint64_constant(8),
            true,
        ),
    ] {
        assert!(
            crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &wrong)
                .is_none()
        );
    }
    let native_count = MachineTerm::Variable(Variable(973_001));
    let narrow = PureFactContext::new().assume_proposition(fact(
        SymbolicMemory::new(),
        MachineTerm::legacy_cast(
            MachineCastSpelling::UInt32From64,
            Box::new(native_count.clone()),
        ),
        false,
    ));
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(narrow),
            &fact(SymbolicMemory::new(), native_count, true,)
        )
        .is_none(),
        "a low-word span cannot establish the full native span"
    );
    let external = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let live = SymbolicMemory::new()
        .with_heap_allocation_claim(external.clone(), AllocationSize::int32(16))
        .unwrap();
    let dead = live
        .clone()
        .free_heap_block(&external, &PureFactContext::new())
        .unwrap();
    let external_fact = |memory| Proposition::MemoryLoadable {
        memory,
        base: external.clone(),
        bytes: crate::kernel::StoredMachineTerm::new(
            crate::kernel::MachineIntegerType::UInt64,
            MachineTerm::uint64_constant(8),
        ),
        wide: true,
    };
    let context = PureFactContext::new().assume_proposition(external_fact(live));
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(context),
            &external_fact(dead)
        )
        .is_none()
    );
}

#[test]
fn native_loadability_prefix_coverage_retains_full_width_bounds() {
    let memory = SymbolicMemory::new();
    let base = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let range = |bytes| Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: crate::kernel::StoredMachineTerm::new(
            crate::kernel::MachineIntegerType::UInt64,
            bytes,
        ),
        wide: true,
    };
    for held in [
        0,
        1,
        u64::from(u32::MAX),
        1u64 << 32,
        i64::MAX as u64,
        u64::MAX,
    ] {
        let context =
            PureFactContext::new().assume_proposition(range(MachineTerm::uint64_constant(held)));
        for requested in [0, 1, held, held.saturating_add(1)] {
            let goal = range(MachineTerm::uint64_constant(requested));
            let proof =
                crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal);
            assert_eq!(proof.is_some(), requested <= held, "{requested} <= {held}");
            if let Some(proof) = proof {
                assert!(proof.check(&context));
            }
        }
    }
    let held = MachineTerm::Variable(Variable(973_101));
    let requested = MachineTerm::Variable(Variable(973_102));
    let source = range(held.clone());
    let goal = range(requested.clone());
    let context = PureFactContext::new().assume_proposition(source.clone());
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal).is_none()
    );
    let bound = Proposition::condition_is(
        ConditionTerm::uint64_less_equal(requested.clone(), held.clone()),
        true,
    );
    let bounded = context.clone().assume_proposition(bound);
    let proof =
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(bounded), &goal).unwrap();
    assert!(proof.check(&bounded));
    assert!(
        !proof.check(&context),
        "the coverage bound must remain a premise"
    );
    let low_word_bound = Proposition::condition_is(
        ConditionTerm::unsigned_less_equal(
            MachineTerm::legacy_cast(MachineCastSpelling::UInt32From64, Box::new(requested)),
            MachineTerm::legacy_cast(MachineCastSpelling::UInt32From64, Box::new(held)),
        ),
        true,
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(context.assume_proposition(low_word_bound)),
            &goal
        )
        .is_none()
    );
}

#[test]
fn native_loadability_prefix_coverage_preserves_lifetime_and_base() {
    let base = Address {
        base: "native-prefix".into(),
        offset: AddressOffset::Constant(0),
    };
    let live = SymbolicMemory::new().with_block("native-prefix", 8);
    let range = |memory: SymbolicMemory, base: Address, bytes| Proposition::MemoryLoadable {
        memory,
        base,
        bytes: crate::kernel::StoredMachineTerm::new(
            crate::kernel::MachineIntegerType::UInt64,
            MachineTerm::uint64_constant(bytes),
        ),
        wide: true,
    };
    let context = PureFactContext::new().assume_proposition(range(live.clone(), base.clone(), 8));
    let written = live
        .clone()
        .store(base.clone(), ProgramValue::Int32(MachineTerm::constant(7)));
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(context),
            &range(written, base.clone(), 4)
        )
        .unwrap()
        .check(&context)
    );
    for wrong in [
        range(live.clone().with_block("native-prefix", 2), base.clone(), 4),
        range(
            live.clone().without_local_block(&base.base),
            base.clone(),
            4,
        ),
        range(SymbolicMemory::new(), base.offset_by_bytes(8), 1),
    ] {
        assert!(
            crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &wrong)
                .is_none()
        );
    }
    let external = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let allocated = SymbolicMemory::new()
        .with_heap_allocation_claim(external.clone(), AllocationSize::int32(16))
        .unwrap();
    let retired = allocated
        .clone()
        .free_heap_block(&external, &PureFactContext::new())
        .unwrap();
    let context = PureFactContext::new().assume_proposition(range(allocated, external.clone(), 8));
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(context),
            &range(retired, external, 4)
        )
        .is_none()
    );
}

#[test]
fn native_loadability_window_checks_offset_end_and_retirement() {
    let memory = SymbolicMemory::new();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(17),
    };
    let range = |memory: SymbolicMemory, base: Address, bytes| Proposition::MemoryLoadable {
        memory,
        base,
        bytes: crate::kernel::StoredMachineTerm::new(
            crate::kernel::MachineIntegerType::UInt64,
            MachineTerm::uint64_constant(bytes),
        ),
        wide: true,
    };
    let context =
        PureFactContext::new().assume_proposition(range(memory.clone(), source.clone(), 16));
    for (offset, length, expected) in [
        (0i64, 16, true),
        (1, 15, true),
        (3, 13, true),
        (-1, 1, false),
        (1, 16, false),
        (17, 1, false),
    ] {
        let goal = range(
            memory.clone(),
            Address {
                base: source.base.clone(),
                offset: AddressOffset::Constant(17 + offset),
            },
            length,
        );
        let proof =
            crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal);
        assert_eq!(
            proof.is_some(),
            expected,
            "offset {offset}, length {length}"
        );
        if let Some(proof) = proof {
            assert!(proof.check(&context));
        }
    }
    let root = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let large = 1u64 << 32;
    let goal_base = Address {
        base: root.base.clone(),
        offset: AddressOffset::scaled_int64_node(MachineTerm::uint64_constant(large), 1, true),
    };
    let context =
        PureFactContext::new().assume_proposition(range(memory.clone(), root.clone(), large + 8));
    let goal = range(memory.clone(), goal_base.clone(), 8);
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
            .unwrap()
            .check(&context)
    );
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(context),
            &range(memory, goal_base, 9)
        )
        .is_none()
    );
    let live = SymbolicMemory::new()
        .with_heap_allocation_claim(root.clone(), AllocationSize::int32(16))
        .unwrap();
    let dead = live
        .clone()
        .free_heap_block(&root, &PureFactContext::new())
        .unwrap();
    let context = PureFactContext::new().assume_proposition(range(live, root.clone(), 16));
    assert!(
        crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(context),
            &range(dead, root.offset_by_bytes(1), 4)
        )
        .is_none()
    );
}

#[test]
fn native_loadability_window_requires_every_full_width_guard() {
    let memory = SymbolicMemory::new();
    let base = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let held = MachineTerm::Variable(Variable(973_201));
    let offset = MachineTerm::Variable(Variable(973_202));
    let requested = MachineTerm::Variable(Variable(973_203));
    let target = Address {
        base: base.base.clone(),
        offset: AddressOffset::scaled_int64_node(offset.clone(), 1, true),
    };
    let source = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base,
        bytes: crate::kernel::StoredMachineTerm::new(
            crate::kernel::MachineIntegerType::UInt64,
            held.clone(),
        ),
        wide: true,
    };
    let goal = Proposition::MemoryLoadable {
        memory,
        base: target,
        bytes: crate::kernel::StoredMachineTerm::new(
            crate::kernel::MachineIntegerType::UInt64,
            requested.clone(),
        ),
        wide: true,
    };
    let le = |left, right| {
        Proposition::condition_is(ConditionTerm::uint64_less_equal(left, right), true)
    };
    let guards = [
        le(
            offset.clone(),
            MachineTerm::uint64_constant(i64::MAX as u64),
        ),
        le(offset.clone(), held.clone()),
        le(requested, MachineTerm::uint64_subtract(held, offset)),
    ];
    let full = guards.iter().cloned().fold(
        PureFactContext::new().assume_proposition(source.clone()),
        PureFactContext::assume_proposition,
    );
    let proof =
        crate::kernel::search::ProofSearch::derive_atomic_proposition(&(full), &goal).unwrap();
    assert!(proof.check(&full));
    for omitted in 0..guards.len() {
        let context = guards
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != omitted)
            .map(|(_, p)| p.clone())
            .fold(
                PureFactContext::new().assume_proposition(source.clone()),
                PureFactContext::assume_proposition,
            );
        assert!(!proof.check(&context));
        assert!(
            crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
                .is_none(),
            "omitted guard {omitted}"
        );
    }
}

#[test]
fn unsigned_u16_packing_bridges_match_disjoint_fields_and_retain_both_bounds() {
    use num_bigint::BigInt;
    fn word(term: &MachineTerm) -> u64 {
        match term {
            bits32_constant!(value) => u64::from(constant_u32(*value)),
            uint64_constant!(value) => constant_u64(*value),
            int64_constant!(value) => constant_i64(*value) as u64,
            binary_term!(Bits32, BitwiseOr, a, b)
            | MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseOr,
                left: a,
                right: b,
            } => word(a) | word(b),
            binary_term!(Bits32, ShiftLeft, a, b) => {
                u64::from((word(a) as u32).wrapping_shl(word(b) as u32))
            }
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::ShiftLeft,
                left: a,
                right: b,
            } => word(a).wrapping_shl(word(b) as u32),
            _ => panic!("unexpected native packing term"),
        }
    }
    fn observed(term: &IntegerTerm) -> BigInt {
        match term {
            IntegerTerm::Constant(value) => value.clone(),
            IntegerTerm::Machine(value) => BigInt::from(match value.ty() {
                MachineIntegerType::UInt32 => word(value.value()),
                MachineIntegerType::UInt64 => word(value.value()),
                _ => panic!("unexpected observation"),
            }),
            IntegerTerm::Add(a, b) => observed(a) + observed(b),
            IntegerTerm::Multiply(a, b) => observed(a) * observed(b),
            _ => panic!("unexpected packing term"),
        }
    }
    for ty in [MachineIntegerType::UInt32, MachineIntegerType::UInt64] {
        let word = |value| match ty {
            MachineIntegerType::UInt32 => MachineTerm::constant(value as u32),
            MachineIntegerType::UInt64 => MachineTerm::uint64_constant(value),
            _ => unreachable!(),
        };
        let maximum = if ty == MachineIntegerType::UInt32 {
            u32::MAX as u64
        } else {
            u64::MAX
        };
        for low in [0, 1, 255, 256, 65535, 65536, maximum] {
            for high in [0, 1, 255, 256, 65535, 65536, maximum] {
                for theorem in [
                    prove_unsigned_pack_u16_to_integer(ty, word(low), word(high)).unwrap(),
                    prove_unsigned_pack_u16_high_first_to_integer(ty, word(low), word(high))
                        .unwrap(),
                ] {
                    let Proposition::Implies(low_guard, rest) = theorem.proposition() else {
                        panic!("missing low bound");
                    };
                    let Proposition::Implies(high_guard, conclusion) = rest.as_ref() else {
                        panic!("missing high bound");
                    };
                    assert_eq!(PureFactContext::new().proves_exact(low_guard), low <= 65535);
                    assert_eq!(
                        PureFactContext::new().proves_exact(high_guard),
                        high <= 65535
                    );
                    let Some((ConditionTerm::IntegerEqual(packed, exact), true)) =
                        conclusion.as_ref().condition_native()
                    else {
                        panic!("missing observation equality");
                    };
                    let expected = match ty {
                        MachineIntegerType::UInt32 => {
                            u64::from((low as u32) | (high as u32).wrapping_shl(16))
                        }
                        MachineIntegerType::UInt64 => low | high.wrapping_shl(16),
                        _ => unreachable!(),
                    };
                    assert_eq!(observed(packed), BigInt::from(expected));
                    assert_eq!(
                        observed(exact),
                        BigInt::from(low) + BigInt::from(65536) * BigInt::from(high)
                    );
                    if low <= 65535 && high <= 65535 {
                        assert_eq!(observed(packed), observed(exact));
                    }
                }
            }
        }
    }
    assert!(
        prove_unsigned_pack_u16_to_integer(
            MachineIntegerType::Int32,
            MachineTerm::constant(0),
            MachineTerm::constant(0)
        )
        .is_none()
    );
    // Overlapping fields and a wrapping high field disprove the unguarded rule.
    assert_ne!(65536u32 | (1u32 << 16), 65536u32 + 65536u32);
    assert_ne!(u64::from(65536u32.wrapping_shl(16)), 65536u64 * 65536);
}

#[test]
fn required_obligation_connectives_use_graph_equalities_and_scoped_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let a = MachineTerm::Variable(Variable(97800));
    let b = MachineTerm::Variable(Variable(97801));
    let c = MachineTerm::Variable(Variable(97802));
    let eq = |x, y| Proposition::condition_is(ConditionTerm::equal(x, y), true);
    let ab = eq(a.clone(), b.clone());
    let bc = eq(b, c.clone());
    let goal = Proposition::Or(
        Box::new(eq(a, c)),
        Box::new(Proposition::condition_is(
            ConditionTerm::Variable(Variable(97803)),
            true,
        )),
    );
    let before = PureFactContext::new().assume_proposition(ab);
    let after = before.clone().assume_proposition(bc);
    assert!(required_obligation_is_exactly_discharged(&after, &goal));
    assert!(!required_obligation_is_exactly_discharged(&before, &goal));
}

#[test]
fn model_fact_restriction_keeps_only_selected_graph_support() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = maybe_int32_type();
    let model = |id| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(id)),
    };
    let (a, b) = (model(97900), model(97901));
    let equality = Proposition::Equal(
        Term::Algebraic(a.clone().into()),
        Term::Algebraic(b.clone().into()),
    );
    let condition = ConditionTerm::AlgebraicEqual(Box::new(a), Box::new(b));
    let both = PureFactContext::new()
        .assume_proposition(equality.clone())
        .assume_condition(condition.clone(), true);
    let proposition_only = both.restricted_to_facts(&[], std::slice::from_ref(&equality));
    assert_eq!(proposition_only.decide(&condition), Some(true));
    assert!(!both.restricted_to_facts(&[], &[]).contains_known(&equality));
    // The selected condition can be new to the base context; restriction
    // still files its model edge.
    let selected = PureFactContext::new().restricted_to_facts(&[(condition, true)], &[]);
    assert!(selected.contains_known(&equality));
}

#[test]
fn uint32_unpacking_rules_retain_bounds_and_recover_all_word_bits() {
    fn evaluate(term: &MachineTerm) -> u32 {
        match term {
            int32_constant!(value) => constant_u32(*value),
            binary_term!(Int32, BitwiseOr, left, right) => evaluate(left) | evaluate(right),
            binary_term!(Int32, BitwiseAnd, left, right) => evaluate(left) & evaluate(right),
            binary_term!(Int32, ShiftLeft, left, right) => {
                evaluate(left).wrapping_shl(evaluate(right))
            }
            binary_term!(UInt32, ShiftRight, left, right) => {
                evaluate(left).wrapping_shr(evaluate(right))
            }
            _ => panic!("unexpected extraction term"),
        }
    }
    let mut boundaries = vec![
        0,
        1,
        255,
        256,
        32767,
        32768,
        65520,
        65521,
        65535,
        65536,
        u32::MAX,
    ];
    boundaries.extend((0..16).map(|bit| 1u32 << bit));
    for &low in &boundaries {
        for &high in &boundaries {
            for theorem in [
                prove_uint32_unpack_uint16_low(
                    MachineTerm::constant(low),
                    MachineTerm::constant(high),
                ),
                prove_uint32_unpack_uint16_high(
                    MachineTerm::constant(low),
                    MachineTerm::constant(high),
                ),
            ] {
                let Proposition::Implies(low_guard, rest) = theorem.proposition() else {
                    panic!("low bound missing")
                };
                let Proposition::Implies(high_guard, conclusion) = rest.as_ref() else {
                    panic!("high bound missing")
                };
                assert_eq!(PureFactContext::new().proves_exact(low_guard), low <= 65535);
                assert_eq!(
                    PureFactContext::new().proves_exact(high_guard),
                    high <= 65535
                );
                let Proposition::ConditionIs(condition, true) = conclusion.as_ref() else {
                    panic!("word identity missing")
                };
                let identity_holds = match condition.native_compat() {
                    ConditionTerm::Constant(value) => *value,
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: extracted,
                        right: original,
                    } => evaluate(extracted) == evaluate(original),
                    _ => panic!("unexpected word identity"),
                };
                if low <= 65535 && high <= 65535 {
                    assert!(identity_holds, "low={low}, high={high}");
                }
            }
        }
    }
    // Bounds cannot be dropped from the paired round trip.
    let oversized = std::hint::black_box(65536u32);
    assert_ne!(oversized & 65535, oversized);
    assert_ne!((oversized.wrapping_shl(16) >> 16) & 65535, oversized);
}

#[test]
fn uint64_unpacking_rules_require_bounded_fields_and_preserve_packed_bits() {
    let mut values = vec![
        0u64,
        1,
        255,
        256,
        32767,
        32768,
        65520,
        65521,
        65535,
        65536,
        1u64 << 32,
        1u64 << 48,
        u64::MAX,
    ];
    values.extend((0..16).map(|bit| 1u64 << bit));
    for &low in &values {
        for &high in &values {
            for name in [
                "click::integer::uint64_unpack_uint16_low",
                "click::integer::uint64_unpack_uint16_high",
            ] {
                let theorem = prove_uint64_integer_bridge(
                    name,
                    MachineTerm::uint64_constant(low),
                    MachineTerm::uint64_constant(high),
                )
                .unwrap();
                let Proposition::Implies(low_guard, rest) = theorem.proposition() else {
                    panic!("low bound missing")
                };
                let Proposition::Implies(high_guard, result) = rest.as_ref() else {
                    panic!("high bound missing")
                };
                let facts = PureFactContext::new();
                assert_eq!(facts.proves_exact(low_guard), low <= 65535);
                assert_eq!(facts.proves_exact(high_guard), high <= 65535);
                if low <= 65535 && high <= 65535 {
                    assert!(facts.proves_exact(result), "{name}: low={low}, high={high}");
                }
            }
        }
    }
    // The low field must not leak into the high field, and the high field
    // must fit before packing; both counterexamples violate an issued guard.
    let oversized = std::hint::black_box(65536u64);
    assert_ne!(oversized & 65535, oversized);
    assert_ne!((oversized << 16 >> 16) & 65535, oversized);
}

#[test]
fn finite_forall_lazy_pairs_keep_nearest_first_order_for_unequal_domains() {
    for (a, b, c, d) in [
        (-3, 2, -1, 4),
        (0, 3, 8, 11),
        (8, 11, 0, 3),
        (0, 1, 0, 1),
        (0, 0, 0, 3),
        (0, 3, 0, 0),
    ] {
        let i = Variable(92_110);
        let j = Variable(92_111);
        let guard = Proposition::And(
            Box::new(int32_half_open_bound(&MachineTerm::Variable(i), a, b)),
            Box::new(int32_half_open_bound(&MachineTerm::Variable(j), c, d)),
        );
        let goal = forall_int32(
            i,
            forall_int32(
                j,
                Proposition::Implies(
                    Box::new(guard),
                    Box::new(Proposition::condition_is(
                        ConditionTerm::Constant(true),
                        true,
                    )),
                ),
            ),
        );
        let actual = crate::kernel::finite_forall_goal_instances(&goal, true)
            .unwrap()
            .map(|(values, _)| values)
            .collect::<Vec<_>>();
        let mut expected = (a..b)
            .flat_map(|i| (c..d).map(move |j| vec![i, j]))
            .collect::<Vec<_>>();
        expected.sort_by_key(|values| ((values[1] - values[0]).abs(), values[0], values[1]));
        assert_eq!(actual, expected, "domains {a}..{b}, {c}..{d}");
    }
}

#[test]
fn false_quantified_frame_does_not_exhaust_a_small_load_registry() {
    crate::kernel::eval::with_load_variable_registry_capacity(1000, || {
        let source = "verifying \"probe.c\"; int32 untouched_element(int32* a) { owns a[0..1000000]; ensures result == old(a[2]); ensures (0..1000000).all(|k| { a[k] == old(a[k]) }); }";
        let c = "int32 untouched_element(int32* a) { unsigned char* b; b = (unsigned char*)(void*) a; b[5] = 7; return a[2]; }";
        let error = crate::surface::verify_c_sources(source, &[("probe.c", c)])
            .expect_err("the whole range is changed");
        assert!(error.message().contains(".all"), "{}", error.message());
    });
}

#[test]
fn lazy_finite_forall_certificates_require_exact_complete_instance_tables() {
    let k = Variable(92_113);
    let bits = MachineTerm::Variable(k);
    let goal = forall_int32(
        k,
        Proposition::Implies(
            Box::new(int32_half_open_bound(&bits, 0, 3)),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_equal(bits, MachineTerm::Variable(Variable(92_114))),
                true,
            )),
        ),
    );
    let context = (0..3).fold(PureFactContext::new(), |context, value| {
        context.assume_condition(
            ConditionTerm::signed_less_equal(
                MachineTerm::constant(value),
                MachineTerm::Variable(Variable(92_114)),
            ),
            true,
        )
    });
    let instances = context
        .finite_forall_instantiations(&goal)
        .map(|instance| {
            crate::kernel::search::ProofSearch::derive_proposition(&(context), &instance)
                .expect("explicit indexed instance")
        })
        .collect::<Vec<_>>();
    let proof = PropositionDerivation {
        conclusion: goal,
        rule: PropositionDerivationRule::FiniteForAll {
            instances: instances.clone(),
        },
    };
    assert!(proof.check(&context));
    let check = |instances| {
        let altered = PropositionDerivation {
            conclusion: proof.conclusion.clone(),
            rule: PropositionDerivationRule::FiniteForAll { instances },
        };
        assert!(!altered.check(&context));
    };
    check(Vec::new());
    check(instances[..2].to_vec());
    let mut extra = instances.clone();
    extra.push(instances[0].clone());
    check(extra);
    let mut reordered = instances.clone();
    reordered.swap(0, 2);
    check(reordered);
    let mut false_instance = instances;
    false_instance[0].conclusion = Proposition::condition_is(ConditionTerm::Constant(false), true);
    check(false_instance);
}

#[test]
fn pointer_predicate_matching_preserves_arguments_states_and_scope() {
    fn fact(
        name: &str,
        state: ExecutionState,
        pointers: &[Address],
        ty: ProgramType,
        tag: u32,
    ) -> Proposition {
        let mut arguments = vec![
            Term::ExecutionState(Box::new(state)),
            Term::ProgramValue((int32(tag)).into()),
        ];
        arguments.extend(pointers.iter().map(|pointer| {
            Term::ProgramValue(ProgramValue::typed_pointer(pointer.clone(), ty).into())
        }));
        Proposition::Predicate {
            name: name.into(),
            arguments,
        }
    }
    let [a, b, c, d] = [120_001, 120_002, 120_003, 120_004].map(|v| Address::symbolic(Variable(v)));
    let ty = ProgramType::Int32Pointer;
    let state = ExecutionState::new();
    let source = fact("Selected", state.clone(), &[a.clone(), c.clone()], ty, 7);
    let goal = fact("Selected", state.clone(), &[b.clone(), d.clone()], ty, 7);
    let ab = Proposition::condition_is(
        ConditionTerm::PointerEqual(
            Box::new(Pointer::new(a.clone(), ty)),
            Box::new(Pointer::new(b.clone(), ty)),
        ),
        true,
    );
    let cd = Proposition::condition_is(
        ConditionTerm::PointerEqual(
            Box::new(Pointer::new(c.clone(), ty)),
            Box::new(Pointer::new(d.clone(), ty)),
        ),
        true,
    );
    let base = PureFactContext::new().assume_proposition(source.clone());
    let first = base.clone().assume_proposition(ab.clone());
    assert!(
        !first.contains_known(&goal),
        "every pointer argument needs equality"
    );
    let joined = first.assume_proposition(cd.clone());
    assert!(joined.contains_known(&goal));
    assert!(!joined.contains_assumed_exact(&goal));
    assert!(!base.contains_known(&goal));
    let second = base.clone().assume_proposition(cd.clone());
    assert!(!second.contains_known(&goal));
    let unwitnessed = PureFactContext::new()
        .assume_proposition(ab.clone())
        .assume_proposition(cd.clone());
    assert!(!unwitnessed.contains_known(&goal));
    let before = PureFactContext::new()
        .assume_proposition(ab)
        .assume_proposition(cd)
        .assume_proposition(source);
    assert!(
        before.contains_known(&goal),
        "equalities may precede witnesses"
    );
    // A predicate's name fixes its parameter types, so an argument's type is
    // the term's, and pointer equality ignores it.
    assert!(joined.contains_known(&fact(
        "Selected",
        state.clone(),
        &[b.clone(), d.clone()],
        ProgramType::UInt32Pointer,
        7,
    )));
    for wrong in [
        fact("Other", state.clone(), &[b.clone(), d.clone()], ty, 7),
        fact("Selected", state.clone(), &[b.clone(), d.clone()], ty, 8),
        fact(
            "Selected",
            state.clone().with_local("different", int32(1)),
            &[b.clone(), d.clone()],
            ty,
            7,
        ),
        fact(
            "Selected",
            state.with_memory(SymbolicMemory::new().with_block("new-epoch", 4)),
            &[b, d],
            ty,
            7,
        ),
    ] {
        assert!(!joined.contains_known(&wrong));
    }
    assert!(!joined.restricted_to_facts(&[], &[]).contains_known(&goal));
    assert!(
        joined.contains_known(&goal),
        "restricting a clone must not restrict its parent"
    );
}

#[test]
fn predicate_and_callback_lookup_share_late_pointer_class_merges() {
    let a = Address::symbolic_function(Variable(121_001));
    let b = Address::symbolic_function(Variable(121_002));
    let fact = |pointer: Address, state: ExecutionState| Proposition::Predicate {
        name: FunctionContract::predicate_name_for("Invoke"),
        arguments: vec![
            Term::ExecutionState(Box::new(state)),
            Term::ProgramValue(
                (ProgramValue::typed_pointer(
                    pointer,
                    ProgramType::FunctionPointer(CallbackSignature::from_encoded(121_000)),
                ))
                .into(),
            ),
        ],
    };
    let source = fact(a.clone(), ExecutionState::new());
    let sibling_source = fact(a.clone(), ExecutionState::new().with_local("tag", int32(1)));
    let goal = fact(b.clone(), ExecutionState::new());
    let alias = Proposition::condition_is(
        ConditionTerm::AddressEqual(Box::new(a), Box::new(b.clone())),
        true,
    );
    let base = PureFactContext::new()
        .assume_proposition(source.clone())
        .assume_proposition(sibling_source.clone());
    assert_eq!(base.function_contract_facts_for(&b).count(), 0);
    let joined = base.clone().assume_proposition(alias.clone());
    assert!(joined.contains_known(&goal));
    assert_eq!(
        joined
            .function_contract_facts_for(&b)
            .map(|(name, _)| name)
            .collect::<Vec<_>>(),
        vec!["Invoke"]
    );
    let sibling_only = PureFactContext::new()
        .assume_proposition(sibling_source)
        .assume_proposition(alias);
    assert!(
        !sibling_only.contains_known(&goal),
        "a different state is not a predicate witness"
    );
    assert_eq!(
        sibling_only.function_contract_facts_for(&b).count(),
        1,
        "the other checked contract witness remains"
    );
    assert!(!base.contains_known(&goal));
}

#[test]
fn pointer_fact_payloads_are_not_revisited_when_fresh_aliases_join_a_large_class() {
    use crate::kernel::equality_graph::EqualityGraph;
    for size in [16, 64, 256] {
        let target = Address::symbolic(Variable(124_000));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::Predicate {
                name: format!("Witness{index}"),
                arguments: vec![Term::ProgramValue(
                    (ProgramValue::typed_pointer(target.clone(), ProgramType::Int32Pointer)).into(),
                )],
            });
        }
        EqualityGraph::take_pointer_fact_merge_visits();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::AddressEqual(
                    Box::new(target.clone()),
                    Box::new(Address::symbolic(Variable(125_000 + index))),
                ),
                true,
            );
        }
        assert_eq!(
            EqualityGraph::take_pointer_fact_merge_visits(),
            0,
            "fresh aliases must not move any of the {size} existing witnesses"
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/proof_reasoning_tests.rs");
}

/// An atomic derivation computed inside the extended DAG bridging may match
/// order-path terms through memory derivations, which is only valid inside
/// that scope. Its memo entry is therefore keyed by the DAG modes, so neither
/// mode reuses the other's answer.
#[test]
fn atomic_derivation_memo_is_keyed_by_the_dag_modes() {
    crate::kernel::assumptions::clear_assumption_memos();
    let value = MachineTerm::Variable(Variable(9_101));
    let goal = Proposition::condition_is(
        ConditionTerm::signed_less_than(value, MachineTerm::constant(5)),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(goal.clone());
    let memoized = |id| {
        crate::kernel::assumptions::proposition_reasoning::atomic_derivation_is_memoized(
            id, &goal, false,
        )
    };

    let (outside, id) = assumptions
        .selected_for_test()
        .proves_atomic_for_derivation_with_id(&goal, false);
    assert!(outside.is_some());
    assert!(memoized(id));
    crate::kernel::api::with_extended_dag_bridging(|| {
        assert!(
            !memoized(id),
            "an answer from outside the scope is not reused inside it"
        );
        let (inside, inside_id) = assumptions
            .selected_for_test()
            .proves_atomic_for_derivation_with_id(&goal, false);
        assert!(inside.is_some());
        assert_eq!(inside_id, id);
        assert!(memoized(id));
    });
    assert!(
        memoized(id),
        "the answer from outside the scope is still served outside it"
    );
}

/// Selecting a whole-range equality uses the retained alpha/load key.
/// Unrelated proposition facts do not enter the query.
#[test]
fn universal_consequents_ignore_unrelated_propositions() {
    let bound = Variable(94_000);
    let universal = crate::kernel::quantifiers::test_forall(
        Default::default(),
        bound,
        Sort::ProgramInt32,
        Proposition::Implies(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(
                    MachineTerm::Variable(bound),
                    MachineTerm::constant(0),
                ),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::equal(
                    MachineTerm::Variable(bound),
                    MachineTerm::Variable(Variable(94_001)),
                ),
                true,
            )),
        ),
    );
    let query = (
        MachineTerm::Variable(Variable(94_002)),
        MachineTerm::constant(1),
    );
    let work = [16_usize, 64, 256]
        .into_iter()
        .map(|unrelated| {
            // Canonical forms stay cold at every sample size: the sign-bit
            // equivalent of `x < 0` names σ, whose canonical form is built
            // on a cache miss.
            crate::kernel::eval::clear_load_canonicalization_caches();
            crate::kernel::memory_history::clear_canonical_form_caches();
            let mut assumptions = PureFactContext::new().assume_proposition(universal.clone());
            for index in 0..unrelated {
                let unrelated = Address {
                    base: format!("universal-unrelated-{index}").into(),
                    offset: AddressOffset::Constant(0),
                };
                assumptions = assumptions.assume_proposition(Proposition::ResourceContains {
                    parent: Box::new(Resource::Memory(memory_range(unrelated.clone(), 0, 2))),
                    child: Box::new(Resource::Memory(memory_range(unrelated, 0, 1))),
                });
            }
            let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.selected_universal_equality_value(
                    Variable(94_002),
                    Proposition::condition_is(
                        ConditionTerm::signed_less_than(query.0.clone(), 0u32.into()),
                        true,
                    ),
                    &query.0,
                    &query.1,
                )
            });
            assert_eq!(
                selected,
                Some((MachineTerm::Variable(Variable(94_001)), true))
            );
            work
        })
        .collect::<Vec<_>>();
    assert!(work[0] > 0);
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated facts changed the universal instantiation's work: {work:?}"
    );
}

/// Selected range equalities and the other instantiation sites ignore
/// universals that only conclude orders.
#[test]
fn universal_instantiation_ignores_universals_of_other_shapes() {
    let ordered = |index: u32| {
        let bound = Variable(96_000 + u64::from(index));
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            bound,
            Sort::ProgramInt32,
            Proposition::Implies(
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(bound),
                        MachineTerm::constant(0),
                    ),
                    true,
                )),
                Box::new(Proposition::condition_is(
                    ConditionTerm::signed_less_equal(
                        MachineTerm::Variable(bound),
                        MachineTerm::constant(index),
                    ),
                    true,
                )),
            ),
        )
    };
    let cell = MachineTerm::Variable(Variable(95_900));
    let goal = Proposition::condition_is(
        ConditionTerm::equal(cell.clone(), MachineTerm::constant(7)),
        true,
    );
    let bound = Variable(95_901);
    let universal_goal = crate::kernel::quantifiers::test_forall(
        Default::default(),
        bound,
        Sort::ProgramInt32,
        Proposition::condition_is(
            ConditionTerm::equal(MachineTerm::Variable(bound), cell.clone()),
            true,
        ),
    );
    let work = [16_u32, 64, 256]
        .into_iter()
        .map(|unrelated| {
            let assumptions = (0..unrelated).fold(PureFactContext::new(), |facts, index| {
                facts.assume_proposition(ordered(index))
            });
            let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions
                    .selected_universal_equality_value(
                        bound,
                        Proposition::condition_is(ConditionTerm::Constant(true), true),
                        &cell,
                        &MachineTerm::constant(7),
                    )
                    .is_some()
                    || assumptions
                        .select_forall_int32_instantiation_evidence(&goal)
                        .is_some()
                    || assumptions.proves_atomic_without_search(&universal_goal)
            });
            assert!(!found);
            work
        })
        .collect::<Vec<_>>();
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "universals of other shapes changed the instantiation's work: {work:?}"
    );
}

/// The fast exact check answers a condition by lookup: it does not read
/// the stated implications and universals, which only a premise context
/// (`proves_atomic_from_premises`) or the proposition search consults. It
/// once scanned every proposition fact on every miss.
#[test]
fn exact_condition_check_ignores_unrelated_implications() {
    let target = ConditionTerm::signed_less_than(
        MachineTerm::Variable(Variable(95_000)),
        MachineTerm::Variable(Variable(95_001)),
    );
    let work = [16_u64, 64, 256]
        .into_iter()
        .map(|unrelated| {
            let mut assumptions = PureFactContext::new();
            for index in 0..unrelated {
                assumptions = assumptions.assume_proposition(Proposition::Implies(
                    Box::new(Proposition::condition_is(
                        ConditionTerm::equal(
                            MachineTerm::Variable(Variable(95_100 + index)),
                            MachineTerm::constant(1),
                        ),
                        true,
                    )),
                    Box::new(Proposition::condition_is(
                        ConditionTerm::equal(
                            MachineTerm::Variable(Variable(95_500 + index)),
                            MachineTerm::constant(2),
                        ),
                        true,
                    )),
                ));
            }
            let goal = Proposition::condition_is(target.clone(), true);
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.proves_atomic_without_search(&goal)
            });
            assert!(!proved);
            work
        })
        .collect::<Vec<_>>();
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated implications changed the exact check's work: {work:?}"
    );
}

#[test]
fn existential_derivation_keeps_witness_conditions_local() {
    let n = Variable(96_000);
    let positive = Proposition::condition_is(
        ConditionTerm::signed_less_than(MachineTerm::constant(0), MachineTerm::Variable(n)),
        true,
    );
    let exact = Proposition::condition_is(
        ConditionTerm::equal(MachineTerm::Variable(n), MachineTerm::constant(7)),
        true,
    );
    let source = crate::kernel::quantifiers::test_exists(
        "n".into(),
        n,
        Sort::ProgramInt32,
        Proposition::And(Box::new(positive.clone()), Box::new(exact)),
    );
    let goal = crate::kernel::quantifiers::test_exists("n".into(), n, Sort::ProgramInt32, positive);
    let Proposition::Exists {
        var, sort, body, ..
    } = &goal
    else {
        unreachable!("test goal is existential");
    };
    let available = PureFactContext::new().assume_proposition(source.clone());
    let rule =
        crate::kernel::search::ProofSearch::derive_exists_from_fact(&available, **var, sort, body)
            .expect("the source witness establishes the goal body");
    let proof = PropositionDerivation {
        conclusion: goal,
        rule,
    };
    assert_eq!(proof.context_premises(), vec![source]);
    assert!(proof.check(&available));
    assert!(!proof.check(&PureFactContext::new()));
}

/// A state-equivalent offset fact is read from the facts filed under the
/// query's offset shape, and an alpha-equal existential from the goal's
/// identity bucket. Both once scanned every fact, so a miss grew with
/// unrelated facts.
#[test]
fn offset_and_existential_matches_ignore_unrelated_facts() {
    let memory = SymbolicMemory::new();
    let load = MachineTerm::read_named(
        ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
        Box::new(Address {
            base: "shape-target".into(),
            offset: AddressOffset::Constant(0),
        }),
        crate::kernel::LoadKind::Int32,
    );
    let scaled = AddressOffset::scaled_int32_node(load, 4);
    let existential = crate::kernel::quantifiers::test_exists(
        String::new(),
        Variable(97_000),
        Sort::ProgramInt32,
        Proposition::condition_is(
            ConditionTerm::signed_less_than(
                MachineTerm::Variable(Variable(97_000)),
                MachineTerm::Variable(Variable(97_001)),
            ),
            true,
        ),
    );
    let work = [16_u64, 64, 256]
        .into_iter()
        .map(|unrelated| {
            let mut context = PureFactContext::new();
            for index in 0..unrelated {
                context = context
                    .assume_condition(
                        ConditionTerm::address_offset_equal(
                            AddressOffset::Variable(Variable(97_100 + index)),
                            AddressOffset::Constant(index as i64),
                        ),
                        true,
                    )
                    .assume_proposition(crate::kernel::quantifiers::test_exists(
                        String::new(),
                        Variable(97_000),
                        Sort::ProgramInt32,
                        Proposition::condition_is(
                            ConditionTerm::equal(
                                MachineTerm::Variable(Variable(97_000)),
                                MachineTerm::Variable(Variable(97_600 + index)),
                            ),
                            true,
                        ),
                    ));
            }
            // Keying the facts assumed since the last query is index upkeep.
            context.build_stated_proposition_index();
            let (offset, offset_work) = crate::instrumentation::measure_deterministic_work(|| {
                context.has_pointer_offset_state_fact(&scaled, &AddressOffset::Constant(4))
            });
            let (exists, exists_work) = crate::instrumentation::measure_deterministic_work(|| {
                context.proves_atomic_without_search(&existential)
            });
            assert_eq!((offset, exists), (false, false));
            (offset_work, exists_work)
        })
        .collect::<Vec<_>>();
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated facts changed the offset and existential matches' work: {work:?}"
    );
}

#[test]
fn complete_pointer_read_source_retains_the_domain_version() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Address::symbolic(Variable(995_031));
    let unrelated = Address::symbolic(Variable(995_032));
    let before = crate::kernel::intern_memory(SymbolicMemory::new().store(
        cell.clone(),
        ProgramValue::typed_pointer(
            Address::symbolic(Variable(995_033)),
            ProgramType::Int32Pointer,
        ),
    ));
    let address = Address::loaded_value(&before, &cell);
    let after = crate::kernel::intern_memory(
        before
            .memory()
            .clone()
            .store(unrelated, ProgramValue::Int32(MachineTerm::constant(1))),
    );
    let old_value = Pointer::from_read(address.clone(), ProgramType::Int32Pointer, &before, &cell);
    let value = Pointer::from_read(address, ProgramType::Int32Pointer, &after, &cell);
    assert_eq!(old_value.address(), value.address());
    assert_ne!(
        old_value, value,
        "an address alone does not identify a complete pointer"
    );
    assert!(old_value.complete_read_source().is_none());
    let (source, source_cell) = value
        .complete_read_source()
        .expect("the domain's introducing read");
    assert_eq!(source, after.unchanged_bytes_source());
    assert_eq!(source_cell, cell);
}

#[test]
fn selected_universal_equality_keeps_bounds_orientation_and_branch_context() {
    let bound = Variable(96_990);
    let query_bound = Variable(96_991);
    let cell = |var| {
        MachineTerm::add(
            MachineTerm::Variable(var),
            MachineTerm::Variable(Variable(96_992)),
        )
    };
    let bounds = |var, lower: u32| {
        Proposition::And(
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_equal(lower.into(), MachineTerm::Variable(var)),
                true,
            )),
            Box::new(Proposition::condition_is(
                ConditionTerm::signed_less_than(MachineTerm::Variable(var), 4u32.into()),
                true,
            )),
        )
    };
    let source = |truth| {
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            bound,
            Sort::ProgramInt32,
            Proposition::Implies(
                Box::new(bounds(bound, 0)),
                Box::new(Proposition::condition_is(
                    ConditionTerm::equal(7u32.into(), cell(bound)),
                    truth,
                )),
            ),
        )
    };
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_proposition(source(true));
    let select = |facts: &PureFactContext, lower, expected| {
        facts.selected_universal_equality_value(
            query_bound,
            bounds(query_bound, lower),
            &cell(query_bound),
            &MachineTerm::constant(expected),
        )
    };
    assert_eq!(select(&branch, 0, 7), Some((7u32.into(), true)));
    assert_eq!(select(&branch, 0, 8), Some((7u32.into(), true)));
    assert_eq!(
        select(&branch, 1, 7),
        None,
        "different bounds need their antecedent established"
    );
    assert_eq!(select(&parent, 0, 7), None);
    let negative = parent.assume_proposition(source(false));
    assert_eq!(select(&negative, 0, 7), Some((7u32.into(), false)));
}
