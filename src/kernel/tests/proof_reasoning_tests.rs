// The proposition search these tests exercise is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. The kernel itself never
// calls it, so the tests import the planner explicitly.
use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

#[test]
fn refuted_disjunction_requires_the_source_and_every_exact_negation() {
    let cases = [71_000, 71_001, 71_002].map(|id| {
        Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(id)),
                Bitvector32Term::Constant(0),
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
    // Inserting an opposite condition ordinarily replaces its polarity.
    // This witness checks the contradiction without rebuilding case contexts.
    let goal = Proposition::Equal(Term::CValue(int32(0)), Term::CValue(int32(1)));
    let derivation = context
        .derive_proposition(&goal)
        .expect("all arms are refuted");
    assert!(derivation.check(&context));
    assert_eq!(derivation.context_premises().len(), 4);
    assert!(!derivation.check(&context.without_exact_fact(&disjunction)));
    for case in &cases {
        let without = context.without_exact_fact(&Proposition::Not(Box::new(case.clone())));
        assert!(!derivation.check(&without));
        assert!(without.derive_proposition(&goal).is_none());
    }
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn nested_simp_derivations_keep_rule_temporaries_off_the_recursive_stack() {
    std::thread::Builder::new()
        .name("nested-simp-small-stack".into())
        .stack_size(1792 * 1024)
        .spawn(|| {
            let samples = [1, 2, 4, 8].map(|depth| {
                let variable = Variable(98_000);
                let value = Bitvector32Term::Variable(variable);
                let positive = Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
                    true,
                );
                let nonnegative = Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value),
                    true,
                );
                // Keep real quantified/atomic work below the connective spine.
                let mut goal = Proposition::ForAll {
                    var: variable,
                    sort: Sort::CInt32,
                    body: Box::new(Proposition::Implies(
                        Box::new(positive),
                        Box::new(nonnegative),
                    )),
                };
                let truth = Proposition::ConditionIs(
                    ConditionTerm::equal(
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                );
                for _ in 0..depth {
                    goal = Proposition::And(
                        Box::new(truth.clone()),
                        Box::new(Proposition::Implies(
                            Box::new(truth.clone()),
                            Box::new(Proposition::Implies(
                                Box::new(truth.clone()),
                                Box::new(goal),
                            )),
                        )),
                    );
                }
                let assumptions = PureFactContext::new();
                let (proof, planning_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        assumptions
                            .derive_simp_proposition(&goal)
                            .expect("nested quantified proof")
                    });
                let (checked, checking_work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        proof.check(&assumptions)
                    });
                assert!(checked);
                (depth, planning_work, checking_work)
            });
            for pair in samples.windows(2) {
                assert!(
                    pair[1].1 <= pair[0].1 * 3 + 16,
                    "planning work: {samples:?}"
                );
                assert!(
                    pair[1].2 <= pair[0].2 * 3 + 16,
                    "checking work: {samples:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
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
    let arguments = vec![AlgebraicValueType::C(CType::Int32)];
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "None".to_string(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Some".to_string(),
            fields: vec![AlgebraicValueType::C(CType::Int32)],
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
    fields: Vec<CValue>,
) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: variant.to_string(),
            fields: fields.into_iter().map(AlgebraicValue::C).collect(),
        },
    }
}

#[test]
fn checked_algebraic_constructor_rules_are_sound() {
    let algebraic_type = maybe_int32_type();
    let left = Bitvector32Term::Variable(Variable(89_000));
    let right = Bitvector32Term::Variable(Variable(89_001));
    let field_equality =
        Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right.clone()), true);
    let constructor_equality = Proposition::Equal(
        Term::Algebraic(maybe_constructor(
            &algebraic_type,
            "Some",
            vec![CValue::Int32(left.clone())],
        )),
        Term::Algebraic(maybe_constructor(
            &algebraic_type,
            "Some",
            vec![CValue::Int32(right.clone())],
        )),
    );

    let injectivity_context =
        PureFactContext::new().assume_proposition(constructor_equality.clone());
    let injectivity = injectivity_context
        .derive_simp_proposition(&field_equality)
        .expect("a checked same-constructor equality entails its field equality");
    assert!(injectivity.check(&injectivity_context));

    let congruence_context = PureFactContext::new().assume_proposition(field_equality);
    let congruence = congruence_context
        .derive_simp_proposition(&constructor_equality)
        .expect("checked field equalities entail equality of their constructors");
    assert!(congruence.check(&congruence_context));

    let malformed = Proposition::Equal(
        Term::Algebraic(maybe_constructor(
            &algebraic_type,
            "Some",
            vec![CValue::UInt32(left)],
        )),
        Term::Algebraic(maybe_constructor(
            &algebraic_type,
            "Some",
            vec![CValue::UInt32(right)],
        )),
    );
    assert!(
        PureFactContext::new()
            .derive_simp_proposition(&malformed)
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
        Term::Algebraic(model.clone()),
        Term::Algebraic(maybe_constructor(&algebraic_type, "Some", vec![int32(7)])),
    );
    let unrelated = Proposition::Equal(
        Term::Algebraic(AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(Variable(89_021)),
        }),
        Term::Algebraic(maybe_constructor(&algebraic_type, "None", vec![])),
    );
    let goal = Proposition::Not(Box::new(Proposition::Equal(
        Term::Algebraic(model),
        Term::Algebraic(maybe_constructor(&algebraic_type, "None", vec![])),
    )));
    let assumptions = PureFactContext::new().assume_proposition(source.clone());
    let derivation = assumptions
        .derive_atomic_proposition(&goal)
        .expect("a known constructor proves disequality from every other constructor");
    assert!(derivation.has_typed_atomic_evidence());
    assert!(derivation.check(&assumptions));
    let facts = crate::kernel::proof::ProofFacts::from_ordered(&[source.clone(), unrelated]);
    assert_eq!(facts.algebraic_equalities_mentioning(&goal), vec![source]);
    let unmatched = Proposition::Not(Box::new(Proposition::Equal(
        Term::Algebraic(AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(Variable(89_022)),
        }),
        Term::Algebraic(maybe_constructor(&algebraic_type, "None", vec![])),
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
        Term::Algebraic(function.clone()),
        Term::Algebraic(middle.clone()),
    );
    let constructor = |field: AlgebraicTerm| AlgebraicTerm {
        algebraic_type: algebraic_type.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Node".into(),
            fields: vec![AlgebraicValue::Algebraic(field)],
        },
    };
    let goal = Proposition::Equal(
        Term::Algebraic(constructor(function)),
        Term::Algebraic(constructor(middle)),
    );
    let unrelated = Proposition::Equal(
        Term::Algebraic(AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(Variable(89_032)),
        }),
        Term::Algebraic(AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(Variable(89_033)),
        }),
    );
    let facts = crate::kernel::proof::ProofFacts::from_ordered(&[source.clone(), unrelated]);
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
                    variant: "None".to_string(),
                    bindings: vec![],
                    body: call.clone(),
                },
                AlgebraicResultMatchArm {
                    variant: "Some".to_string(),
                    bindings: vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
                        Variable(89_011),
                    )))],
                    body: call.clone(),
                },
            ],
        },
    };
    let equality = |a: &AlgebraicTerm, b: &AlgebraicTerm| {
        Proposition::Equal(Term::Algebraic(a.clone()), Term::Algebraic(b.clone()))
    };
    let context = PureFactContext::new();
    for term in [&call, &matched] {
        let goal = equality(term, term);
        assert!(crate::kernel::proof::fact_reasoning::normalizes_context_free(&goal));
        assert!(
            context
                .derive_simp_proposition(&goal)
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
            vec![CValue::UInt32(Bitvector32Term::Constant(0))],
        ))];
    }
    let mut malformed_match = matched;
    if let AlgebraicTermNode::Match { arms, .. } = &mut malformed_match.node {
        arms.pop();
    }
    for term in [malformed_call, malformed_match] {
        let goal = equality(&term, &term);
        assert!(!crate::kernel::proof::fact_reasoning::normalizes_context_free(&goal));
        assert!(context.derive_simp_proposition(&goal).is_none());
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
    let equality = Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right));
    assert_eq!(PureFactContext::new().decide(&condition), None);
    for expected in [true, false] {
        let premise = if expected {
            equality.clone()
        } else {
            Proposition::Not(Box::new(equality.clone()))
        };
        let facts = PureFactContext::new().assume_proposition(premise.clone());
        let condition_fact = Proposition::ConditionIs(condition.clone(), expected);
        // `decide` answers an algebraic equality only from an indexed
        // condition fact. An `Equal` premise over algebraic terms is a
        // proposition, not a condition fact, so it does not decide the
        // condition; the polarity forms checked below are the route an
        // explicit proof uses to move between the two spellings.
        assert_eq!(facts.decide(&condition), None);
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
                &Proposition::ConditionIs(condition.clone(), !expected)
            )
        );
    }
    let distinct = ConditionTerm::AlgebraicEqual(
        Box::new(maybe_constructor(&ty, "None", vec![])),
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![CValue::Int32(Bitvector32Term::Constant(0))],
        )),
    );
    // Constructor distinctness is proposition-level theory, covered by
    // `distinct_algebraic_constructors_make_the_context_inconsistent` below.
    // `decide` does not reach it for the condition spelling.
    assert_eq!(PureFactContext::new().decide(&distinct), None);
}

#[test]
fn algebraic_condition_substitution_visits_scalar_fields() {
    let ty = maybe_int32_type();
    let variable = Variable(89_102);
    let condition = ConditionTerm::AlgebraicEqual(
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![CValue::Int32(Bitvector32Term::Variable(variable))],
        )),
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![CValue::Int32(Bitvector32Term::Constant(0))],
        )),
    );
    let mut variables = BTreeSet::new();
    collect_condition_bitvector_variables(&condition, &mut variables);
    assert_eq!(variables, BTreeSet::from([variable]));
    let rewritten = substitute_bitvector_variable_in_condition(
        &condition,
        variable,
        &Bitvector32Term::Constant(0),
    );
    // Substitution reaches the scalar field inside the constructor, so the
    // rewritten condition is syntactically the all-constant one. `decide`
    // answers an algebraic equality only from an indexed condition fact, so
    // the rewrite itself is what this test observes.
    let substituted = ConditionTerm::AlgebraicEqual(
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![CValue::Int32(Bitvector32Term::Constant(0))],
        )),
        Box::new(maybe_constructor(
            &ty,
            "Some",
            vec![CValue::Int32(Bitvector32Term::Constant(0))],
        )),
    );
    assert_eq!(rewritten, substituted);
    let mut rewritten_variables = BTreeSet::new();
    collect_condition_bitvector_variables(&rewritten, &mut rewritten_variables);
    assert!(rewritten_variables.is_empty());
    let value = Bitvector32Term::If {
        condition: Box::new(condition),
        then_term: Box::new(Bitvector32Term::Constant(1)),
        else_term: Box::new(Bitvector32Term::Constant(0)),
    };
    assert!(!crate::kernel::term_is_shallow_structural_cache_key(&value));
}

#[test]
fn distinct_algebraic_constructors_make_the_context_inconsistent() {
    let algebraic_type = maybe_int32_type();
    let conflict = Proposition::Equal(
        Term::Algebraic(maybe_constructor(&algebraic_type, "None", vec![])),
        Term::Algebraic(maybe_constructor(&algebraic_type, "Some", vec![int32(7)])),
    );
    assert!(
        PureFactContext::new()
            .assume_proposition(conflict)
            .is_inconsistent()
    );
}

#[test]
fn algebraic_constructor_injectivity_ignores_unrelated_facts() {
    let algebraic_type = maybe_int32_type();
    let left = Bitvector32Term::Variable(Variable(89_100));
    let right = Bitvector32Term::Variable(Variable(89_101));
    let goal = Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right.clone()), true);
    let source = Proposition::Equal(
        Term::Algebraic(maybe_constructor(
            &algebraic_type,
            "Some",
            vec![CValue::Int32(left)],
        )),
        Term::Algebraic(maybe_constructor(
            &algebraic_type,
            "Some",
            vec![CValue::Int32(right)],
        )),
    );
    let samples = [16, 64, 256]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new().assume_proposition(source.clone());
            for index in 0..size {
                assumptions = assumptions.assume_proposition(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: vec![],
                });
            }
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.derive_simp_proposition(&goal)
            });
            assert!(derivation.is_some());
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "constructor injectivity lookup scaled with unrelated facts: {samples:?}"
        );
    }
}

#[test]
fn function_contract_lookup_ignores_unrelated_pointer_facts() {
    fn contract_fact(name: &str, pointer: Pointer) -> Proposition {
        Proposition::Predicate {
            name: CFunctionContract::predicate_name_for(name),
            arguments: vec![
                Term::CState(Box::new(CState::new())),
                Term::CValue(CValue::typed_pointer(
                    pointer,
                    CType::FunctionPointer(CallbackSignature::from_encoded(90_000)),
                )),
            ],
        }
    }

    let samples = [16, 64, 256, 1024]
        .into_iter()
        .map(|size| {
            let target = Pointer::symbolic_function(Variable(90_001));
            let mut assumptions =
                PureFactContext::new().assume_proposition(contract_fact("Target", target.clone()));
            for index in 0..size {
                assumptions = assumptions.assume_proposition(contract_fact(
                    "Unrelated",
                    Pointer::symbolic_function(Variable(91_000 + index as u64)),
                ));
            }
            let (contracts, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions
                    .function_contract_facts_for(&target)
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>()
            });
            assert_eq!(contracts, vec!["Target".to_string()]);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 == pair[0].1),
        "exact contract lookup must not scan unrelated pointer facts: {samples:?}"
    );
}

#[test]
fn pointer_substitution_replaces_the_block_and_preserves_the_offset() {
    let from = Variable(90_100);
    let replacement = Pointer {
        block: PointerBlock::Symbolic(Variable(90_101)),
        offset: PointerOffsetTerm::Constant(8),
    };
    let occurrence = Pointer {
        block: PointerBlock::Symbolic(from),
        offset: PointerOffsetTerm::Constant(4),
    };
    let proposition = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(occurrence, Pointer::null()),
        true,
    );

    let substituted =
        crate::kernel::substitute_pointer_variable_in_proposition(&proposition, from, &replacement);
    let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, _), true) = substituted else {
        panic!("pointer substitution changed the proposition shape");
    };
    assert_eq!(
        *left,
        Pointer {
            block: PointerBlock::Symbolic(Variable(90_101)),
            offset: PointerOffsetTerm::Constant(12),
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
    let left = Bitvector32Term::Variable(Variable(90_000));
    let right = Bitvector32Term::Variable(Variable(90_001));
    let less_equal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let not_less_than = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        false,
    );
    let goal = Proposition::ConditionIs(ConditionTerm::equal(left, right), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(less_equal.clone())
        .assume_proposition(not_less_than.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
    let left = Bitvector32Term::Variable(Variable(90_002));
    let right = Bitvector32Term::Variable(Variable(90_003));
    let greater_equal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
        true,
    );
    let not_greater_than = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
        false,
    );
    let goal = Proposition::ConditionIs(ConditionTerm::equal(left, right), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(greater_equal.clone())
        .assume_proposition(not_greater_than.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
    let value = Bitvector32Term::Variable(Variable(90_004));
    let positive = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(positive.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("0 < value should derive 0 <= value");
    assert_eq!(
        derivation
            .int32_positive_is_nonnegative_step()
            .map(SignedOrderDerivationStep::premise),
        Some(&positive)
    );
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));

    let reversed_goal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value, Bitvector32Term::Constant(0)),
        true,
    );
    let reversed = assumptions
        .derive_simp_proposition(&reversed_goal)
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
    let value = Bitvector32Term::Variable(Variable(90_008));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(2)),
        false,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("not (value < 2) should derive value >= 1");
    let step = derivation
        .int32_negated_strict_successor_bound_step()
        .expect("the atomic decision should retain its successor-bound premise");
    assert_eq!(step.lower(), &Bitvector32Term::Constant(2));
    assert_eq!(step.upper(), &value);
    assert!(!step.is_strict());
    assert_eq!(step.premise(), &premise);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn int32_successor_le_implies_lt_retains_its_exact_premise() {
    let value = Bitvector32Term::Variable(Variable(90_009));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), value.clone()),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("2 <= value should derive 1 < value");
    let step = derivation
        .int32_successor_le_implies_lt_step()
        .expect("the atomic decision should retain its adjacent lower bound");
    assert_eq!(step.lower(), &Bitvector32Term::Constant(2));
    assert_eq!(step.upper(), &value);
    assert!(!step.is_strict());
    assert_eq!(step.premise(), &premise);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn int32_constant_lower_bound_weakening_retains_its_exact_premise() {
    let value = Bitvector32Term::Variable(Variable(90_010));
    let lower = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(3), value.clone()),
        true,
    );
    let reversed = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(3)),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value.clone()),
        true,
    );

    for premise in [lower, reversed] {
        let assumptions = PureFactContext::new().assume_proposition(premise.clone());
        let derivation = assumptions
            .derive_simp_proposition(&goal)
            .expect("3 <= value should derive 0 <= value");
        let step = derivation
            .int32_constant_lower_bound_weakening_step()
            .expect("the atomic decision should retain its stronger lower bound");
        assert_eq!(step.lower(), &Bitvector32Term::Constant(3));
        assert_eq!(step.upper(), &value);
        assert!(!step.is_strict());
        assert_eq!(step.premise(), &premise);
        assert!(derivation.check(&assumptions));
        assert!(!derivation.check(&PureFactContext::new()));
    }
}

#[test]
fn int32_le_and_neq_strict_derivation_retains_both_exact_premises() {
    let left = Bitvector32Term::Variable(Variable(90_006));
    let right = Bitvector32Term::Variable(Variable(90_007));
    let less_equal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let not_equal =
        Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right.clone()), false);
    let goal = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(less_equal.clone())
        .assume_proposition(not_equal.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
            Proposition::ConditionIs(ConditionTerm::Variable(Variable(300_000 + index)), true)
        })
        .collect();
    let conjunction = proposition_and_all(propositions);

    assert_eq!(conjunction_depth(&conjunction), 10);
}

#[test]
fn exact_contradiction_lookup_scales_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(100_000 + index as u64)),
                        Bitvector32Term::Constant(index as u32),
                    ),
                    true,
                );
            }
            let contradiction_left = Bitvector32Term::Variable(Variable(200_000));
            let contradiction_right = Bitvector32Term::Constant(7);
            assumptions = assumptions
                .assume_condition(
                    ConditionTerm::equal(contradiction_left.clone(), contradiction_right.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(contradiction_left, contradiction_right),
                    true,
                );
            let (inconsistent, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.is_inconsistent()
            });
            assert!(inconsistent);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "exact contradiction lookup is superlinear: {samples:?}"
        );
    }
}

/// `x < 0` and `x >= 0` are a comparison and its arithmetic negation rather
/// than one condition at both polarities, so `contradicts` recognizes the
/// pair through the fixed list of equivalent spellings. A merely tighter
/// bound such as `x >= 1` is not that negation and stays a non-contradiction.
#[test]
fn contradicts_recognizes_a_comparison_and_its_arithmetic_negation() {
    let value = Bitvector32Term::Variable(Variable(310_000));
    let negative = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let at_least_one = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value, Bitvector32Term::Constant(1)),
        true,
    );

    let opposite = crate::kernel::proof::ProofFacts::from_ordered(&[negative.clone(), nonnegative]);
    assert!(
        opposite.contradicts(&negative),
        "`x < 0` held beside `x >= 0` contradicts"
    );

    let tighter = crate::kernel::proof::ProofFacts::from_ordered(&[negative.clone(), at_least_one]);
    assert!(
        !tighter.contradicts(&negative),
        "`x >= 1` is not the arithmetic negation of `x < 0`"
    );
}

#[test]
fn known_scalar_equality_uses_congruence_without_building_a_fact_index() {
    let a = Bitvector32Term::Variable(Variable(990_001));
    let b = Bitvector32Term::Variable(Variable(990_002));
    let c = Bitvector32Term::Variable(Variable(990_003));
    let left = Bitvector32Term::Add(Box::new(a.clone()), Box::new(c.clone()));
    let right = Bitvector32Term::Add(Box::new(b.clone()), Box::new(c));
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
fn known_scalar_queries_have_bounded_work_beside_growing_classes() {
    for size in [8u64, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |i| Bitvector32Term::Variable(Variable(991_000 + i));
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context.assume_condition(ConditionTerm::equal(var(i), var(i + 1)), true);
            context = context.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(992_000 + i)),
                    Bitvector32Term::Constant(i as u32),
                ),
                true,
            );
        }
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(context.int32_values_known_equal(&sum(var(0)), &sum(var(size))));
            assert!(!context.int32_values_known_equal(&sum(var(0)), &sum(var(size + 1))));
        });
        assert!(work < 128, "size={size}, work={work}");
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    }
}

#[test]
fn equality_graph_queries_do_not_build_the_condition_fact_index() {
    let root = Bitvector32Term::Variable(Variable(210_000));
    let mut assumptions = PureFactContext::new();
    let mut connected = Vec::new();
    for index in 0..32 {
        let term = Bitvector32Term::Variable(Variable(210_001 + index));
        assumptions =
            assumptions.assume_condition(ConditionTerm::equal(root.clone(), term.clone()), true);
        connected.push(term);
    }
    for index in 0..128 {
        assumptions = assumptions.assume_condition(
            ConditionTerm::signed_less_than(
                Bitvector32Term::Variable(Variable(220_000 + index)),
                Bitvector32Term::Constant(index as u32),
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

/// `exact_signed_constant` answers from an index keyed by the term, so what
/// it examines does not grow with the unrelated condition facts beside the
/// one that pins the term. It used to scan every condition fact, uncharged,
/// on each range-membership and offset-equality query that asked it.
#[test]
fn exact_signed_constant_is_a_keyed_lookup_among_unrelated_facts() {
    use crate::kernel::assumptions::exact_signed_constant;

    let pinned = Bitvector32Term::Variable(Variable(230_000));
    let reversed = Bitvector32Term::Variable(Variable(230_001));
    let wide = Bitvector32Term::Variable(Variable(230_002));
    let unpinned = Bitvector32Term::Variable(Variable(230_003));
    let mut samples = Vec::new();
    for size in [64_u32, 128, 256, 512] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            let other = Bitvector32Term::Variable(Variable(231_000 + u64::from(index)));
            // Unrelated constant equalities, unrelated order facts, and
            // facts that mention the queried terms without pinning them.
            assumptions = assumptions
                .assume_condition(
                    ConditionTerm::equal(other.clone(), Bitvector32Term::Constant(index)),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(pinned.clone(), other.clone()),
                    true,
                )
                .assume_condition(ConditionTerm::equal(unpinned.clone(), other), false);
        }
        assumptions = assumptions
            .assume_condition(
                ConditionTerm::equal(pinned.clone(), Bitvector32Term::Constant(7)),
                true,
            )
            .assume_condition(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Constant(-3_i32 as u32)),
                    Box::new(reversed.clone()),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::Bitvector64Equal(
                    Box::new(wide.clone()),
                    Box::new(Bitvector32Term::Int64Constant(1 << 40)),
                ),
                true,
            );
        PureFactContext::reset_exact_constant_fact_visits();
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            [&pinned, &reversed, &wide, &unpinned]
                .map(|term| exact_signed_constant(term, &assumptions))
        });
        assert_eq!(answers, [Some(7), Some(-3), Some(1 << 40), None]);
        let visits = PureFactContext::exact_constant_fact_visits();
        assert_eq!(
            visits, 3,
            "each pinned term reads its own entry and nothing else at {size} facts"
        );
        samples.push((size, work));
        // Withdrawing the pinning fact withdraws its entry.
        let forgotten = assumptions.without_exact_fact(&Proposition::ConditionIs(
            ConditionTerm::equal(pinned.clone(), Bitvector32Term::Constant(7)),
            true,
        ));
        assert_eq!(exact_signed_constant(&pinned, &forgotten), None);
    }
    assert!(
        samples.iter().all(|(_, work)| *work == samples[0].1),
        "exact_signed_constant work must not grow with unrelated facts: {samples:?}"
    );
}

#[test]
fn int32_increment_upper_bound_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_000));
    let upper = Bitvector32Term::Variable(Variable(90_001));
    let theorem = prove_int32_increment_upper_bound(value.clone(), upper.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), upper.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            upper,
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_increment_strictly_increases_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_005));
    let upper = Bitvector32Term::Variable(Variable(90_006));
    let theorem = prove_int32_increment_strictly_increases(value.clone(), upper.clone());
    let premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            value.clone(),
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_increment_lower_bound_axiom_has_the_exact_implications() {
    let value = Bitvector32Term::Variable(Variable(90_010));
    let lower = Bitvector32Term::Variable(Variable(90_011));
    let upper = Bitvector32Term::Variable(Variable(90_012));
    let theorem = prove_int32_increment_lower_bound(value.clone(), lower.clone(), upper.clone());
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), value.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            lower,
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(lower_premise),
            Box::new(Proposition::Implies(
                Box::new(upper_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_increment_greater_equal_lower_bound_axiom_has_exact_implications() {
    let value = Bitvector32Term::Variable(Variable(90_013));
    let lower = Bitvector32Term::Variable(Variable(90_014));
    let upper = Bitvector32Term::Variable(Variable(90_015));
    let theorem = prove_int32_increment_greater_equal_lower_bound(
        value.clone(),
        lower.clone(),
        upper.clone(),
    );
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            lower,
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(lower_premise),
            Box::new(Proposition::Implies(
                Box::new(upper_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_increment_strict_greater_lower_bound_axiom_has_exact_implications() {
    let value = Bitvector32Term::Variable(Variable(90_016));
    let lower = Bitvector32Term::Variable(Variable(90_017));
    let upper = Bitvector32Term::Variable(Variable(90_018));
    let theorem = prove_int32_increment_strict_greater_lower_bound(
        value.clone(),
        lower.clone(),
        upper.clone(),
    );
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            lower,
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(lower_premise),
            Box::new(Proposition::Implies(
                Box::new(upper_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_increment_preserves_order_axiom_has_the_exact_implications() {
    let value = Bitvector32Term::Variable(Variable(90_020));
    let lower = Bitvector32Term::Variable(Variable(90_021));
    let upper = Bitvector32Term::Variable(Variable(90_022));
    let theorem =
        prove_int32_increment_preserves_order(value.clone(), lower.clone(), upper.clone());
    let order_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), value.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(lower, Bitvector32Term::Constant(1)),
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(order_premise),
            Box::new(Proposition::Implies(
                Box::new(upper_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_positive_predecessor_is_nonnegative_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_025));
    let theorem = prove_int32_positive_predecessor_is_nonnegative(value.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            Bitvector32Term::Subtract(Box::new(value), Box::new(Bitvector32Term::Constant(1))),
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_nonnegative_predecessor_upper_bound_axiom_has_the_exact_implications() {
    let value = Bitvector32Term::Variable(Variable(90_030));
    let bound = Bitvector32Term::Variable(Variable(90_031));
    let theorem = prove_int32_nonnegative_predecessor_upper_bound(value.clone(), bound.clone());
    let nonnegative_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let bound_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value.clone(), bound.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Subtract(Box::new(value), Box::new(Bitvector32Term::Constant(1))),
            bound,
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(nonnegative_premise),
            Box::new(Proposition::Implies(
                Box::new(bound_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_lt_implies_le_axiom_has_the_exact_implication() {
    let left = Bitvector32Term::Variable(Variable(90_027));
    let right = Bitvector32Term::Variable(Variable(90_028));
    let theorem = prove_int32_lt_implies_le(left.clone(), right.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(left, right), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_not_lt_implies_ge_axiom_has_the_exact_implication() {
    let left = Bitvector32Term::Variable(Variable(90_029));
    let right = Bitvector32Term::Variable(Variable(90_030));
    let theorem = prove_int32_not_lt_implies_ge(left.clone(), right.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        false,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(left, right), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_ge_and_not_gt_implies_eq_axiom_has_exact_implications() {
    let left = Bitvector32Term::Variable(Variable(90_037));
    let right = Bitvector32Term::Variable(Variable(90_038));
    let theorem = prove_int32_ge_and_not_gt_implies_eq(left.clone(), right.clone());
    let ge_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
        true,
    );
    let not_gt_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
        false,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(ge_premise),
            Box::new(Proposition::Implies(
                Box::new(not_gt_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_lt_transitive_axiom_has_the_exact_implications() {
    let first = Bitvector32Term::Variable(Variable(90_031));
    let middle = Bitvector32Term::Variable(Variable(90_032));
    let last = Bitvector32Term::Variable(Variable(90_033));
    let theorem = prove_int32_lt_transitive(first.clone(), middle.clone(), last.clone());
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(first_premise),
            Box::new(Proposition::Implies(
                Box::new(second_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_ge_transitive_axiom_has_the_exact_implications() {
    let last = Bitvector32Term::Variable(Variable(90_034));
    let middle = Bitvector32Term::Variable(Variable(90_035));
    let first = Bitvector32Term::Variable(Variable(90_036));
    let theorem = prove_int32_ge_transitive(last.clone(), middle.clone(), first.clone());
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(last.clone(), middle.clone()),
        true,
    );
    let second_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(middle, first.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(last, first), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(first_premise),
            Box::new(Proposition::Implies(
                Box::new(second_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_ge_implies_reversed_le_axiom_has_the_exact_implication() {
    let greater = Bitvector32Term::Variable(Variable(90_039));
    let lower = Bitvector32Term::Variable(Variable(90_040));
    let theorem = prove_int32_ge_implies_reversed_le(greater.clone(), lower.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(greater.clone(), lower.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(lower, greater), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_le_implies_reversed_ge_axiom_has_the_exact_implication() {
    let lower = Bitvector32Term::Variable(Variable(90_041));
    let greater = Bitvector32Term::Variable(Variable(90_042));
    let theorem = prove_int32_le_implies_reversed_ge(lower.clone(), greater.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), greater.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(greater, lower), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_increment_below_max_is_defined_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_024));
    let theorem = prove_int32_increment_below_max_is_defined(value.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(value),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        false,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_one_plus_strictly_increases_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_124));
    let theorem = prove_int32_one_plus_strictly_increases(value.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            value.clone(),
            Bitvector32Term::Add(Box::new(Bitvector32Term::Constant(1)), Box::new(value)),
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

/// One pure-theorem scenario: a two-step rewrite chain whose conclusion is
/// also an exactly available requirement, so a real kernel proof object can
/// close it by assumption and issue the completion these constructors consume.
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
    let value = Bitvector32Term::Variable(value_var);
    let left = Bitvector32Term::Variable(left_var);
    let amount = Bitvector32Term::Variable(amount_var);
    let total = Bitvector32Term::Variable(total_var);
    let product = Bitvector32Term::Multiply(Box::new(left.clone()), Box::new(amount.clone()));
    let value_equality =
        Proposition::ConditionIs(ConditionTerm::equal(value.clone(), product.clone()), true);
    let product_equality = Proposition::ConditionIs(ConditionTerm::equal(product, total), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Multiply(Box::new(value.clone()), Box::new(amount.clone())),
            left.clone(),
        ),
        true,
    );
    let requirements = vec![
        Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_add_overflows(left, amount.clone()),
                false,
            )),
            Box::new(value_equality.clone()),
        ),
        Proposition::ConditionIs(
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
/// object that closed its root judgment by an exact assumption.
fn checked_pure_completion(
    requirements: &[Proposition],
    conclusion: &Proposition,
) -> crate::kernel::proof::CheckedProposition {
    use crate::kernel::proof::{
        OutcomeProofState, PersistentOrderedSet, ProofBranch, ProofBranchState, ProofFacts,
        ProofObject, ProofObligation, PropositionAssumptionContext, PropositionObligation,
    };

    let branch = ProofBranch::new(
        ProofObligation::Proposition(PropositionObligation::new(conclusion.clone(), ())),
        ProofBranchState {
            facts: ProofFacts::from_ordered(requirements),
            unfolded_predicates: PersistentOrderedSet::default(),
            execution: None,
        },
    );
    let proof: ProofObject<(), ProofObligation<(), std::sync::Arc<OutcomeProofState<()>>>, ()> =
        ProofObject::root((), branch);
    let Ok(closed) = proof.apply_assumption(PropositionAssumptionContext::Exact) else {
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
        |body, var| Proposition::ForAll {
            var: *var,
            sort: Sort::CInt32,
            body: Box::new(body),
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
    let unavailable = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Variable(scenario.variables[0]),
            Bitvector32Term::Constant(7),
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
fn int32_nonnegative_add_within_max_is_defined_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_025));
    let amount = Bitvector32Term::Variable(Variable(90_026));
    let theorem = prove_int32_nonnegative_add_within_max_is_defined(value.clone(), amount.clone());
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), amount.clone()),
        true,
    );
    let within_headroom = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            value.clone(),
            Bitvector32Term::Subtract(
                Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
                Box::new(amount.clone()),
            ),
        ),
        true,
    );
    let defined =
        Proposition::ConditionIs(ConditionTerm::signed_add_overflows(value, amount), false);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(nonnegative),
            Box::new(Proposition::Implies(
                Box::new(within_headroom),
                Box::new(defined),
            )),
        )
    );
}

#[test]
fn int32_positive_predecessor_strictly_decreases_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_026));
    let theorem = prove_int32_positive_predecessor_strictly_decreases(value.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Subtract(
                Box::new(value.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            value,
        ),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_successor_le_implies_lt_axiom_has_the_exact_implications() {
    let lower = Bitvector32Term::Variable(Variable(90_030));
    let value = Bitvector32Term::Variable(Variable(90_031));
    let theorem = prove_int32_successor_le_implies_lt(lower.clone(), value.clone());
    let successor = Bitvector32Term::add(lower.clone(), Bitvector32Term::Constant(1));
    let no_overflow_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(lower.clone(), successor.clone()),
        true,
    );
    let bound_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(successor, value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(lower, value), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(no_overflow_premise),
            Box::new(Proposition::Implies(
                Box::new(bound_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_lt_successor_implies_le_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_032));
    let upper = Bitvector32Term::Variable(Variable(90_033));
    let theorem = prove_int32_lt_successor_implies_le(value.clone(), upper.clone());
    let successor = Bitvector32Term::add(upper.clone(), Bitvector32Term::Constant(1));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), successor),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(value, upper), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_lt_implies_neq_axiom_has_the_exact_implication() {
    let left = Bitvector32Term::Variable(Variable(90_034));
    let right = Bitvector32Term::Variable(Variable(90_035));
    let theorem = prove_int32_lt_implies_neq(left.clone(), right.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        false,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_le_and_not_lt_implies_eq_axiom_has_the_exact_implications() {
    let left = Bitvector32Term::Variable(Variable(90_032));
    let right = Bitvector32Term::Variable(Variable(90_033));
    let theorem = prove_int32_le_and_not_lt_implies_eq(left.clone(), right.clone());
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let not_lt_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        false,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(le_premise),
            Box::new(Proposition::Implies(
                Box::new(not_lt_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_le_and_neq_implies_lt_axiom_has_the_exact_implications() {
    let left = Bitvector32Term::Variable(Variable(90_034));
    let right = Bitvector32Term::Variable(Variable(90_035));
    let theorem = prove_int32_le_and_neq_implies_lt(left.clone(), right.clone());
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let neq_premise = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
        false,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(le_premise),
            Box::new(Proposition::Implies(
                Box::new(neq_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_le_antisymmetric_axiom_has_the_exact_implications() {
    let left = Bitvector32Term::Variable(Variable(90_040));
    let right = Bitvector32Term::Variable(Variable(90_041));
    let theorem = prove_int32_le_antisymmetric(left.clone(), right.clone());
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let reverse_le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(right.clone(), left.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
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
fn int32_positive_is_nonnegative_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_040));
    let theorem = prove_int32_positive_is_nonnegative(value.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
    );
}

#[test]
fn int32_le_lt_transitive_axiom_has_the_exact_implications() {
    let first = Bitvector32Term::Variable(Variable(90_050));
    let middle = Bitvector32Term::Variable(Variable(90_051));
    let last = Bitvector32Term::Variable(Variable(90_052));
    let theorem = prove_int32_le_lt_transitive(first.clone(), middle.clone(), last.clone());
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(first_premise),
            Box::new(Proposition::Implies(
                Box::new(second_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_le_transitive_axiom_has_the_exact_implications() {
    let first = Bitvector32Term::Variable(Variable(90_053));
    let middle = Bitvector32Term::Variable(Variable(90_054));
    let last = Bitvector32Term::Variable(Variable(90_055));
    let theorem = prove_int32_le_transitive(first.clone(), middle.clone(), last.clone());
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(first, last), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(first_premise),
            Box::new(Proposition::Implies(
                Box::new(second_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn int32_lt_le_transitive_axiom_has_the_exact_implications() {
    let first = Bitvector32Term::Variable(Variable(90_055));
    let middle = Bitvector32Term::Variable(Variable(90_056));
    let last = Bitvector32Term::Variable(Variable(90_057));
    let theorem = prove_int32_lt_le_transitive(first.clone(), middle.clone(), last.clone());
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(first_premise),
            Box::new(Proposition::Implies(
                Box::new(second_premise),
                Box::new(conclusion),
            )),
        )
    );
}

#[test]
fn proposition_derivation_honors_active_deadline() {
    let assumptions = PureFactContext::new();
    let proposition = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    assert!(assumptions.derive_proposition(&proposition).is_some());
    assert!(
        assumptions
            .derive_atomic_proposition(&proposition)
            .is_some()
    );

    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(assumptions.derive_proposition(&proposition).is_none());
        assert!(
            assumptions
                .derive_atomic_proposition(&proposition)
                .is_none()
        );
        assert!(crate::kernel::reasoning::resolution_interrupted());
    });
}

#[test]
fn strict_reverse_order_derives_a_false_comparison() {
    let left = Bitvector32Term::Variable(Variable(200));
    let right = Bitvector32Term::Variable(Variable(201));
    let reverse = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(right.clone(), left.clone()),
        true,
    );
    let target = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), false);
    let assumptions = PureFactContext::new().assume_proposition(reverse.clone());
    let derivation = assumptions
        .derive_proposition(&target)
        .expect("a strict reverse order should prove the comparison false");
    assert_eq!(derivation.context_premises(), vec![reverse]);
    assert!(derivation.check(&assumptions));
    assert!(
        assumptions
            .clone()
            .defer_non_exact_loadability_obligations()
            .derive_proposition(&target)
            .is_some(),
        "proof construction remains available when symbolic execution defers search"
    );
}

#[test]
fn signed_order_derivation_retains_its_exact_edge_path() {
    let left = Bitvector32Term::Variable(Variable(202));
    let middle = Bitvector32Term::Variable(Variable(203));
    let right = Bitvector32Term::Variable(Variable(204));
    let first = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), middle.clone()),
        true,
    );
    let second = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(middle.clone(), right.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the signed-order chain should derive its conclusion");
    let path = derivation
        .signed_order_path()
        .expect("the atomic decision should retain its selected order path");
    assert_eq!(path.len(), 2);
    assert_eq!(path[0].lower(), &left);
    assert_eq!(path[0].upper(), &middle);
    assert!(!path[0].is_strict());
    assert_eq!(path[0].premise(), &first);
    assert_eq!(path[1].lower(), &middle);
    assert_eq!(path[1].upper(), &right);
    assert!(path[1].is_strict());
    assert_eq!(path[1].premise(), &second);
    assert!(derivation.check(&assumptions));
}

#[test]
fn signed_order_derivation_retains_the_exact_negative_polarity_premise() {
    let left = Bitvector32Term::Variable(Variable(205));
    let right = Bitvector32Term::Variable(Variable(206));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        false,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(right.clone(), left.clone()),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the negated non-strict bound should derive reversed strict order");
    let path = derivation
        .signed_order_path()
        .expect("the atomic decision should retain its normalized order edge");
    assert_eq!(path.len(), 1);
    assert_eq!(path[0].lower(), &right);
    assert_eq!(path[0].upper(), &left);
    assert!(path[0].is_strict());
    assert_eq!(path[0].premise(), &premise);
    assert!(derivation.check(&assumptions));
}

#[test]
fn increment_upper_bound_derivation_retains_its_exact_strict_premise() {
    let value = Bitvector32Term::Variable(Variable(207));
    let upper = Bitvector32Term::Variable(Variable(208));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1)),
            upper.clone(),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
    let value = Bitvector32Term::Variable(Variable(207_100));
    let upper = Bitvector32Term::Variable(Variable(207_101));
    let middle = Bitvector32Term::Variable(Variable(207_102));
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1)),
            upper.clone(),
        ),
        true,
    );
    let premises = [
        Proposition::ConditionIs(
            ConditionTerm::signed_less_than(value.clone(), upper.clone()),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(upper.clone(), value.clone()),
            false,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(value.clone(), upper.clone()),
            false,
        ),
    ];
    for premise in premises {
        let assumptions = PureFactContext::new().assume_proposition(premise.clone());
        let derivation = assumptions
            .derive_simp_proposition(&goal)
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
    assert!(!indirect.proves_atomic_for_derivation(&goal, true));
}

#[test]
fn increment_upper_bound_direct_lookup_ignores_unrelated_order_facts() {
    let value = Bitvector32Term::Variable(Variable(207_200));
    let upper = Bitvector32Term::Variable(Variable(207_201));
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(207_300 + index as u64)),
                        Bitvector32Term::Variable(Variable(207_400 + index as u64)),
                    ),
                    true,
                );
            }
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_less_than(value.clone(), upper.clone()),
                true,
            );
            // Measure the direct rule, not construction or other atomic arms.
            let (step, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.exact_direct_order_step(&value, &upper, true)
            });
            assert!(step.is_some());
            assert_eq!(work, 1, "the first indexed candidate is the direct edge");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(1),
            "direct order lookup depends on ambient facts: {samples:?}"
        );
    }
}

#[test]
fn increment_constant_upper_bound_retains_its_exact_nonstrict_premise() {
    let value = Bitvector32Term::Variable(Variable(208_100));
    let direct = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(3)),
        true,
    );
    let reversed = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(Bitvector32Term::Constant(3), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1)),
            Bitvector32Term::Constant(5),
        ),
        true,
    );

    for premise in [direct, reversed] {
        let assumptions = PureFactContext::new().assume_proposition(premise.clone());
        let derivation = assumptions
            .derive_simp_proposition(&goal)
            .expect("value <= 3 should derive value + 1 <= 5");
        let step = derivation
            .int32_increment_constant_upper_bound_step()
            .expect("the atomic decision should retain its non-strict constant bound");
        assert_eq!(step.lower(), &value);
        assert_eq!(step.upper(), &Bitvector32Term::Constant(3));
        assert!(!step.is_strict());
        assert_eq!(step.premise(), &premise);
        assert!(derivation.check(&assumptions));
        assert!(!derivation.check(&PureFactContext::new()));
    }
}

#[test]
fn increment_strictly_increases_derivation_retains_its_exact_strict_premise() {
    let value = Bitvector32Term::Variable(Variable(209));
    let upper = Bitvector32Term::Variable(Variable(210));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            value.clone(),
            Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
    let value = Bitvector32Term::Variable(Variable(211));
    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(int_max.clone(), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(value.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        false,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the strict maximum bound should prove increment definedness");
    let step = derivation
        .int32_increment_below_max_is_defined_step()
        .expect("the atomic decision should retain its named-rule premise");
    assert_eq!(step.lower(), &value);
    assert_eq!(step.upper(), &int_max);
    assert!(step.is_strict());
    assert_eq!(step.premise(), &premise);
    assert!(derivation.check(&assumptions));
}

#[test]
fn one_plus_rules_retain_their_exact_max_bound_and_operand_order() {
    let value = Bitvector32Term::Variable(Variable(211_050));
    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(int_max.clone(), value.clone()),
        true,
    );
    let one_plus = Bitvector32Term::Add(
        Box::new(Bitvector32Term::Constant(1)),
        Box::new(value.clone()),
    );
    let defined_goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(Bitvector32Term::Constant(1)),
            Box::new(value.clone()),
        ),
        false,
    );
    let strict_goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), one_plus),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(premise.clone());

    let defined = assumptions
        .derive_simp_proposition(&defined_goal)
        .expect("the maximum bound should prove one-plus definedness");
    let defined_step = defined
        .int32_one_plus_below_max_is_defined_step()
        .expect("definedness must retain the operand-order-specific rule");
    assert_eq!(defined_step.lower(), &value);
    assert_eq!(defined_step.upper(), &int_max);
    assert!(defined_step.is_strict());
    assert_eq!(defined_step.premise(), &premise);
    assert!(defined.check(&assumptions));

    let strict = assumptions
        .derive_simp_proposition(&strict_goal)
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
    let value = Bitvector32Term::Variable(Variable(211_100));
    let amount = Bitvector32Term::Variable(Variable(211_101));
    let headroom = Bitvector32Term::Subtract(
        Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
        Box::new(amount.clone()),
    );
    let amount_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(amount.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let within_headroom = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(headroom.clone(), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(value.clone()),
            Box::new(amount.clone()),
        ),
        false,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(amount_nonnegative.clone())
        .assume_proposition(within_headroom.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the two named-theorem bounds should prove symbolic addition definedness");
    let (nonnegative_step, headroom_step) = derivation
        .int32_nonnegative_add_within_max_steps()
        .expect("the atomic decision should retain both named-theorem premises");
    assert_eq!(nonnegative_step.lower(), &Bitvector32Term::Constant(0));
    assert_eq!(nonnegative_step.upper(), &amount);
    assert!(!nonnegative_step.is_strict());
    assert_eq!(nonnegative_step.premise(), &amount_nonnegative);
    assert_eq!(headroom_step.lower(), &value);
    assert_eq!(headroom_step.upper(), &headroom);
    assert!(!headroom_step.is_strict());
    assert_eq!(headroom_step.premise(), &within_headroom);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn symbolic_subtract_definedness_retains_both_exact_named_theorem_bounds() {
    let value = Bitvector32Term::Variable(Variable(211_110));
    let amount = Bitvector32Term::Variable(Variable(211_111));
    let amount_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(amount.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let within_value = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), amount.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedSubtractOverflows(
            Box::new(value.clone()),
            Box::new(amount.clone()),
        ),
        false,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(amount_nonnegative.clone())
        .assume_proposition(within_value.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the two named-theorem bounds should prove symbolic subtraction definedness");
    let (nonnegative_step, within_value_step) = derivation
        .int32_nonnegative_subtract_within_value_steps()
        .expect("the atomic decision should retain both named-theorem premises");
    assert_eq!(nonnegative_step.lower(), &Bitvector32Term::Constant(0));
    assert_eq!(nonnegative_step.upper(), &amount);
    assert!(!nonnegative_step.is_strict());
    assert_eq!(nonnegative_step.premise(), &amount_nonnegative);
    assert_eq!(within_value_step.lower(), &amount);
    assert_eq!(within_value_step.upper(), &value);
    assert!(!within_value_step.is_strict());
    assert_eq!(within_value_step.premise(), &within_value);
    assert!(derivation.check(&assumptions));
    assert!(!derivation.check(&PureFactContext::new()));
}

#[test]
fn increment_lower_bound_derivation_retains_both_exact_bounds() {
    let lower = Bitvector32Term::Variable(Variable(212));
    let value = Bitvector32Term::Variable(Variable(213));
    let upper = Bitvector32Term::Variable(Variable(214));
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            lower.clone(),
            Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(lower_premise.clone())
        .assume_proposition(upper_premise.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
    let lower = Bitvector32Term::Variable(Variable(218));
    let value = Bitvector32Term::Variable(Variable(219));
    let upper = Bitvector32Term::Variable(Variable(220));
    let incremented_value = Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1));
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goals = [
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(incremented_value.clone(), lower.clone()),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(incremented_value, lower.clone()),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                Bitvector32Term::add(lower.clone(), Bitvector32Term::Constant(1)),
                Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1)),
            ),
            true,
        ),
    ];
    let assumptions = PureFactContext::new()
        .assume_proposition(lower_premise.clone())
        .assume_proposition(upper_premise.clone());

    for (index, goal) in goals.iter().enumerate() {
        let derivation = assumptions
            .derive_simp_proposition(goal)
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
    let lower = Bitvector32Term::Variable(Variable(220_100));
    let value = Bitvector32Term::Variable(Variable(220_101));
    let upper = Bitvector32Term::Variable(Variable(220_102));
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(lower.clone(), value.clone()),
        true,
    );
    let upper_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(upper.clone(), value.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(
            Bitvector32Term::add(value.clone(), Bitvector32Term::Constant(1)),
            lower.clone(),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(lower_premise.clone())
        .assume_proposition(upper_premise.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
    let value = Bitvector32Term::Variable(Variable(221));
    let bound = Bitvector32Term::Variable(Variable(222));
    let zero = Bitvector32Term::Constant(0);
    let predecessor = Bitvector32Term::Subtract(
        Box::new(value.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let positive = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(value.clone(), zero.clone()),
        true,
    );
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), zero.clone()),
        true,
    );
    let bounded = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(bound.clone(), value.clone()),
        true,
    );

    let positive_assumptions = PureFactContext::new().assume_proposition(positive.clone());
    let nonnegative_goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(zero.clone(), predecessor.clone()),
        true,
    );
    let nonnegative_derivation = positive_assumptions
        .derive_simp_proposition(&nonnegative_goal)
        .expect("strict positivity should prove a nonnegative predecessor");
    let nonnegative_step = nonnegative_derivation
        .int32_positive_predecessor_is_nonnegative_step()
        .expect("the decision should retain its exact positivity premise");
    assert_eq!(nonnegative_step.lower(), &zero);
    assert_eq!(nonnegative_step.upper(), &value);
    assert!(nonnegative_step.is_strict());
    assert_eq!(nonnegative_step.premise(), &positive);
    assert!(nonnegative_derivation.check(&positive_assumptions));

    let decrease_goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(predecessor.clone(), value.clone()),
        true,
    );
    let decrease_derivation = positive_assumptions
        .derive_simp_proposition(&decrease_goal)
        .expect("strict positivity should prove predecessor decrease");
    let decrease_step = decrease_derivation
        .int32_positive_predecessor_strictly_decreases_step()
        .expect("the decision should retain its exact positivity premise");
    assert_eq!(decrease_step.premise(), &positive);
    assert!(decrease_derivation.check(&positive_assumptions));

    let bounded_assumptions = PureFactContext::new()
        .assume_proposition(nonnegative.clone())
        .assume_proposition(bounded.clone());
    let bounded_goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(predecessor, bound.clone()),
        true,
    );
    let bounded_derivation = bounded_assumptions
        .derive_simp_proposition(&bounded_goal)
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

    let one_le = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    let one_le_assumptions = PureFactContext::new().assume_proposition(one_le.clone());
    for (goal, nonnegative_result) in [(&nonnegative_goal, true), (&decrease_goal, false)] {
        let derivation = one_le_assumptions
            .derive_simp_proposition(goal)
            .expect("one at most the value should prove the predecessor conclusion");
        let step = if nonnegative_result {
            derivation.int32_one_le_predecessor_is_nonnegative_step()
        } else {
            derivation.int32_one_le_predecessor_strictly_decreases_step()
        }
        .expect("the derived predecessor decision should retain its exact one-le source");
        assert_eq!(step.lower(), &Bitvector32Term::Constant(1));
        assert_eq!(step.upper(), &value);
        assert!(!step.is_strict());
        assert_eq!(step.premise(), &one_le);
        assert!(derivation.check(&one_le_assumptions));
    }
}

#[test]
fn predecessor_derivation_retains_equal_one_path_instead_of_a_derived_bound() {
    let value = Bitvector32Term::Variable(Variable(223));
    let one = Bitvector32Term::Constant(1);
    let predecessor = Bitvector32Term::Subtract(Box::new(value.clone()), Box::new(one.clone()));
    let equal_one =
        Proposition::ConditionIs(ConditionTerm::equal(one.clone(), value.clone()), true);
    let assumptions = PureFactContext::new().assume_proposition(equal_one.clone());

    for (goal, nonnegative_result) in [
        (
            Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), predecessor.clone()),
                true,
            ),
            true,
        ),
        (
            Proposition::ConditionIs(
                ConditionTerm::signed_less_than(predecessor.clone(), value.clone()),
                true,
            ),
            false,
        ),
    ] {
        let derivation = assumptions
            .derive_simp_proposition(&goal)
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
    let value = Bitvector32Term::Variable(Variable(224));
    let one = Bitvector32Term::Constant(1);
    let zero = Bitvector32Term::Constant(0);
    let predecessor = Bitvector32Term::Subtract(Box::new(value.clone()), Box::new(one.clone()));
    let equal_one =
        Proposition::ConditionIs(ConditionTerm::equal(one.clone(), value.clone()), true);
    let assumptions = PureFactContext::new().assume_proposition(equal_one.clone());

    for goal in [
        Proposition::ConditionIs(
            ConditionTerm::equal(predecessor.clone(), zero.clone()),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::equal(zero.clone(), predecessor.clone()),
            true,
        ),
    ] {
        let derivation = assumptions
            .derive_simp_proposition(&goal)
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
    let left = Bitvector32Term::Variable(Variable(215));
    let middle = Bitvector32Term::Variable(Variable(216));
    let right = Bitvector32Term::Variable(Variable(217));
    let first = Proposition::ConditionIs(ConditionTerm::equal(middle.clone(), left.clone()), true);
    let second =
        Proposition::ConditionIs(ConditionTerm::equal(middle.clone(), right.clone()), true);
    let goal = Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right.clone()), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
fn scalar_graph_literal_evaluation_supplies_checkable_simp_equality() {
    let left = Bitvector32Term::Variable(Variable(218));
    let right = Bitvector32Term::Variable(Variable(219));
    let one = Bitvector32Term::Constant(1);
    let left_is_one =
        Proposition::ConditionIs(ConditionTerm::equal(left.clone(), one.clone()), true);
    let right_is_one =
        Proposition::ConditionIs(ConditionTerm::equal(one.clone(), right.clone()), true);
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Add(Box::new(left.clone()), Box::new(right.clone())),
            Bitvector32Term::Constant(2),
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
        &Bitvector32Term::Add(Box::new(left.clone()), Box::new(right.clone())),
        &Bitvector32Term::Constant(2),
    ));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    // Explicit derivation construction may enumerate its premise evidence;
    // that is separate from the Boolean equality query measured above.
    assert_checkable_derivation(&assumptions, &goal);
    assert!(
        PureFactContext::new()
            .derive_simp_proposition(&goal)
            .is_none()
    );
    assert!(!assumptions.int32_values_known_equal(
        &Bitvector32Term::Add(Box::new(left), Box::new(right)),
        &Bitvector32Term::Constant(3),
    ));
}

#[test]
fn signed_less_equal_and_inequality_derive_strict_order() {
    let left = Bitvector32Term::Variable(Variable(9_004));
    let right = Bitvector32Term::Variable(Variable(9_005));
    let less_equal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let unequal =
        Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right.clone()), false);
    let strict = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(less_equal)
        .assume_proposition(unequal);

    assert_checkable_derivation(&assumptions, &strict);
}

#[test]
fn condition_search_skips_irrelevant_implication_antecedents() {
    let target_condition = ConditionTerm::signed_less_than(
        Bitvector32Term::Variable(Variable(9_001)),
        Bitvector32Term::Variable(Variable(9_002)),
    );
    let unrelated_condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(9_003)),
        Bitvector32Term::Variable(Variable(9_004)),
    );
    let true_fact = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::Implies(
            Box::new(true_fact.clone()),
            Box::new(Proposition::ConditionIs(unrelated_condition, true)),
        ))
        .assume_proposition(Proposition::Implies(
            Box::new(true_fact),
            Box::new(Proposition::ConditionIs(target_condition.clone(), true)),
        ));

    PureFactContext::reset_condition_implication_antecedent_checks();
    assert!(assumptions.proves(&Proposition::ConditionIs(target_condition, true)));
    assert_eq!(
        PureFactContext::condition_implication_antecedent_checks(),
        1,
        "only an implication whose conclusion can establish the target should inspect its antecedent"
    );
}

#[test]
fn merging_required_obligations_preserves_the_certification_frontier() {
    let value = Bitvector32Term::Variable(Variable(9_010));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::equal(value.clone(), Bitvector32Term::Constant(1)),
        true,
    ));
    let derived = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value),
        true,
    );
    assert!(assumptions.proves(&derived));

    let required = ProofObligation::verification_condition(derived.clone());
    let merged = merge_obligations(&[], &[required], &assumptions)
        .expect("required verification conditions should compose");
    assert_eq!(merged.len(), 1);
    assert_eq!(merged[0].proposition(), &derived);
}

#[test]
fn condition_fact_matching_ignores_unrelated_local_memory() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100_000)), 4),
    };
    let owner_field = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::add(owner.offset.clone(), PointerOffsetTerm::Constant(4)),
    };
    let ignored_local = Pointer {
        block: "local:ignored".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let empty_memory = CMemory::new();
    let old_memory = empty_memory.clone().store(
        owner.clone(),
        int32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(empty_memory),
            Box::new(owner),
            crate::kernel::LoadKind::Bits32,
        )),
    );
    let before_local = CMemory::new()
        .with_block("call-havoc:8000000", 0)
        .with_block("local:ignored", 4);
    let after_local = before_local
        .clone()
        .with_block("local:ignored", 4)
        .store(ignored_local, int32(Bitvector32Term::Variable(Variable(1))));
    let old_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(old_memory),
        Box::new(owner_field.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_local),
                Box::new(owner_field.clone()),
                crate::kernel::LoadKind::Bits32,
            ),
            old_load.clone(),
        ),
        true,
    );
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_local),
                Box::new(owner_field),
                crate::kernel::LoadKind::Bits32,
            ),
            old_load,
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(fact);

    assert_checkable_derivation(&assumptions, &target);
}

#[test]
fn bounded_order_check_ignores_unrelated_local_memory() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100_001)), 4),
    };
    let position = owner.clone();
    let length = owner.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let local = CMemory::local_pointer("temporary");
    let fact_memory = CMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block(local.block.clone(), 4)
        .store(local, int32(7));
    let target_memory = CMemory::new().with_block("call-havoc:0", 0);
    let symbolic_length = Bitvector32Term::Variable(Variable(100_002));
    let load = |memory: &CMemory, pointer: &Pointer| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(load(&fact_memory, &position), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(load(&fact_memory, &length), symbolic_length.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), symbolic_length),
            true,
        );
    let target = ConditionTerm::signed_less_than(
        load(&target_memory, &position),
        load(&target_memory, &length),
    );

    assert!(assumptions.proves_order_condition_for_memory_resolution(&target, true));
}

#[test]
fn equality_chains_across_observationally_equivalent_memory_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100_000)), 4),
    };
    let observed = CMemory::local_pointer("observed");
    let before_materialized = CMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block("call-havoc:1", 0)
        .with_block(observed.block.clone(), 4)
        .store(observed, int32(Bitvector32Term::Variable(Variable(10))));
    let before_sparse = CMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block("call-havoc:1", 0);
    let after = before_sparse.clone().with_block("call-havoc:3", 0);
    let before_materialized_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before_materialized),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let before_sparse_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before_sparse),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let after_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(after),
        Box::new(owner),
        crate::kernel::LoadKind::Bits32,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(before_materialized_load, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(after_load.clone(), before_sparse_load),
            true,
        );
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(after_load, Bitvector32Term::Constant(1)),
        true,
    );

    assert_checkable_derivation(&assumptions, &target);
}

#[test]
fn proposition_derivation_proves_implication_from_false_antecedent() {
    let condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(1)),
        Bitvector32Term::Constant(0),
    );
    let antecedent = Proposition::ConditionIs(condition.clone(), false);
    let conclusion = Proposition::Implies(
        Box::new(antecedent),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(2)),
                Bitvector32Term::Variable(Variable(3)),
            ),
            true,
        )),
    );
    let assumptions = PureFactContext::new().assume_condition(condition, true);

    let derivation = assumptions
        .derive_simp_proposition(&conclusion)
        .expect("a false antecedent should prove an implication");
    assert!(derivation.check(&assumptions));
}

#[test]
fn builtin_obligation_solver_proves_trivial_props() {
    let assumptions = PureFactContext::new();
    let memory = CMemory::new().with_block("block", 8);
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };

    assert!(assumptions.proves(&Proposition::Equal(
        Term::Bitvector32(Bitvector32Term::Constant(7)),
        Term::Bitvector32(Bitvector32Term::Constant(7)),
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::Constant(true),
        true
    )));
    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    }));
    assert!(assumptions.proves(&Proposition::CMemoryCanStore {
        memory,
        pointer,
        byte_width: 4,
    }));
}

/// Range narrowing at element granularity: the one loadability route whose
/// goal extent may stay symbolic.
///
/// A segment `p[x..y]` of four-byte elements lowers to the base `p + x * 4`
/// and the extent `(y - x) * 4`, so these helpers build exactly the shape the
/// surface produces. Each test then asks `proves`, which is the same decision
/// the implicit check and the explicit `transport ... using` step both reach.
mod loadable_range_narrowing {
    use super::*;

    fn variable(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    fn segment(memory: &CMemory, start: &Bitvector32Term, end: &Bitvector32Term) -> Proposition {
        let origin = Pointer {
            block: "data".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: origin.offset_by_int32_elements(start.clone()),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::subtract(end.clone(), start.clone()),
                Bitvector32Term::Constant(4),
            ),
            wide: false,
        }
    }

    fn order(lower: &Bitvector32Term, upper: &Bitvector32Term) -> (ConditionTerm, bool) {
        (
            ConditionTerm::signed_less_equal(lower.clone(), upper.clone()),
            true,
        )
    }

    /// The assumed range must also be a valid 32-bit byte extent: its element
    /// count pinned to `0..=u32::MAX / 4` for four-byte elements. These are the
    /// two facts a proof states for that; without them the extent term is
    /// modular and nothing follows from comparing endpoints.
    fn extent_is_valid(a: &Bitvector32Term, b: &Bitvector32Term) -> Vec<(ConditionTerm, bool)> {
        let count = Bitvector32Term::subtract(b.clone(), a.clone());
        let limit = Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(4));
        vec![
            order(&Bitvector32Term::Constant(0), &count),
            order(&count, &limit),
        ]
    }

    fn inside(
        a: &Bitvector32Term,
        b: &Bitvector32Term,
        c: &Bitvector32Term,
        d: &Bitvector32Term,
    ) -> Vec<(ConditionTerm, bool)> {
        let mut orders = vec![order(a, c), order(c, d), order(d, b)];
        orders.extend(extent_is_valid(a, b));
        orders
    }

    /// `a`, `b`, `c`, `d`: the assumed range is `p[a..b]` and the goal is
    /// `p[c..d]`.
    fn endpoints() -> [Bitvector32Term; 4] {
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
        let memory = CMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let assumptions = assume_orders(segment(&memory, &a, &b), &inside(&a, &b, &c, &d));

        assert!(assumptions.proves(&segment(&memory, &c, &d)));
    }

    #[test]
    fn a_sub_range_past_the_assumed_end_is_refused() {
        let memory = CMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        // `d <= b` is exactly the fact that is missing.
        let assumptions = assume_orders(segment(&memory, &a, &b), &[order(&a, &c), order(&c, &d)]);

        assert!(!assumptions.proves(&segment(&memory, &c, &d)));
    }

    /// A reversed goal range lowers to a negative extent. Both ends sit inside
    /// the assumed range, so only the required `c <= d` refuses it.
    #[test]
    fn a_reversed_goal_range_is_refused() {
        let memory = CMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let mut orders = vec![order(&a, &c), order(&d, &c), order(&c, &b)];
        orders.extend(extent_is_valid(&a, &b));
        let assumptions = assume_orders(segment(&memory, &a, &b), &orders);

        assert!(!assumptions.proves(&segment(&memory, &c, &d)));
    }

    /// Loadability is a claim about one memory snapshot. A snapshot in which
    /// the block is no longer there does not inherit the assumed range, so the
    /// order facts alone never carry the conclusion across.
    #[test]
    fn a_different_memory_snapshot_is_refused() {
        let assumed = CMemory::new().with_block("data", 4096);
        let elsewhere = CMemory::new().with_block("other", 4096);
        let [a, b, c, d] = endpoints();
        let assumptions = assume_orders(segment(&assumed, &a, &b), &inside(&a, &b, &c, &d));

        assert!(!assumptions.proves(&segment(&elsewhere, &c, &d)));
    }

    /// The wrapped corner, and the reason the rule asks for the assumed range's
    /// byte-count guards at all.
    ///
    /// An extent is a `Bitvector32Term`, so `(b - a) * 4` is modular. At
    /// `b - a == 1 << 30` it is `1 << 32`, which is `0`: the assumed fact then
    /// claims an empty extent and is vacuously true, while a sub-range of it is
    /// a real claim. Order facts alone cannot tell those apart, so the rule
    /// refuses unless the count is pinned to `0..=u32::MAX / 4`.
    #[test]
    fn a_wrapped_assumed_extent_is_refused() {
        let memory = CMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        // Everything the narrowing rule reads except the extent bound: the goal
        // sits inside the assumed range, and the count is known nonnegative.
        let count = Bitvector32Term::subtract(b.clone(), a.clone());
        let orders = vec![
            order(&a, &c),
            order(&c, &d),
            order(&d, &b),
            order(&Bitvector32Term::Constant(0), &count),
        ];
        let assumptions = assume_orders(segment(&memory, &a, &b), &orders);

        assert!(!assumptions.proves(&segment(&memory, &c, &d)));
    }

    /// A bound on the count is not enough on its own either. With `a` the least
    /// `int32` and `b` the greatest, `a <= b` holds and `b - a <= limit` holds,
    /// because `b - a` is really `-1`; only the nonnegativity fact excludes it.
    #[test]
    fn a_bounded_but_negative_count_is_refused() {
        let memory = CMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let count = Bitvector32Term::subtract(b.clone(), a.clone());
        let limit = Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(4));
        let orders = vec![
            order(&a, &c),
            order(&c, &d),
            order(&d, &b),
            order(&count, &limit),
        ];
        let assumptions = assume_orders(segment(&memory, &a, &b), &orders);

        assert!(!assumptions.proves(&segment(&memory, &c, &d)));
    }

    /// A count bounded past the limit is refused even though it is nonnegative:
    /// scaling it by the element width is what leaves the 32-bit extent.
    #[test]
    fn a_count_past_the_extent_limit_is_refused() {
        let memory = CMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let count = Bitvector32Term::subtract(b.clone(), a.clone());
        let past =
            Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(4) + 1);
        let orders = vec![
            order(&a, &c),
            order(&c, &d),
            order(&d, &b),
            order(&Bitvector32Term::Constant(0), &count),
            order(&count, &past),
        ];
        let assumptions = assume_orders(segment(&memory, &a, &b), &orders);

        assert!(!assumptions.proves(&segment(&memory, &c, &d)));
    }

    /// The two extents must be scaled by one element width. A goal counting
    /// one-byte elements is not a sub-range of a four-byte-element fact just
    /// because its endpoints compare, so the rule declines rather than
    /// rescaling a product it would then have to bound against overflow.
    #[test]
    fn a_different_element_width_is_refused() {
        let memory = CMemory::new().with_block("data", 4096);
        let [a, b, c, d] = endpoints();
        let origin = Pointer {
            block: "data".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let byte_goal = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: origin.offset_by_elements(c.clone(), 1),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::subtract(d.clone(), c.clone()),
                Bitvector32Term::Constant(1),
            ),
            wide: false,
        };
        let assumptions = assume_orders(segment(&memory, &a, &b), &inside(&a, &b, &c, &d));

        assert!(!assumptions.proves(&byte_goal));
    }
}

#[test]
fn empty_memory_range_is_vacuously_loadable() {
    let proposition = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: "not-live".into(),
            offset: PointerOffsetTerm::Variable(Variable(1)),
        },
        bytes: Bitvector32Term::Constant(0),
        wide: false,
    };

    assert!(PureFactContext::new().proves(&proposition));
}

#[test]
fn deferred_obligations_keep_contextual_memory_proofs_explicit() {
    let memory = CMemory::new();
    let base = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: Bitvector32Term::Constant(8),
        wide: false,
    };
    let element = Proposition::CMemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
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
        Bitvector32Term::Variable(Variable(96_001)),
        Bitvector32Term::Constant(10),
    );
    let conclusion = ConditionTerm::signed_less_than(
        Bitvector32Term::Variable(Variable(96_002)),
        Bitvector32Term::Constant(10),
    );
    let assumptions = PureFactContext::new().assume_condition(conclusion.clone(), true);
    let structured = Proposition::Implies(
        Box::new(Proposition::ConditionIs(guard, true)),
        Box::new(Proposition::ConditionIs(conclusion.clone(), true)),
    );
    assert!(
        assumptions.proves(&structured),
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
            Proposition::ConditionIs(conclusion, true)
        )
        .is_some()
    );
    assert!(exact.is_empty());
}

/// Obligation emission is flat in unrelated ambient context.
///
/// The migrated route answers from the exact index and the atomic shape
/// dispatch, so growing the number of unrelated condition facts must not grow
/// the work of deciding whether to emit one structured obligation.
#[test]
fn structured_obligation_emission_scales_flat_in_unrelated_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Variable(Variable(96_100 + index as u64)),
                        Bitvector32Term::Constant(1_000),
                    ),
                    true,
                );
            }
            let structured = Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(96_001)),
                        Bitvector32Term::Constant(10),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(96_002)),
                        Bitvector32Term::Constant(10),
                    ),
                    true,
                )),
            );
            let mut obligations = Vec::new();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                add_proof_obligation(&mut obligations, &assumptions, structured).unwrap();
            });
            assert_eq!(obligations.len(), 1);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "obligation emission grew with unrelated facts: {samples:?}"
        );
    }
}

#[test]
fn memory_derivation_records_the_selected_range_candidate() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let unrelated = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: Pointer {
            block: "unrelated".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        bytes: Bitvector32Term::Constant(64),
        wide: false,
    };
    let selected = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(8),
        wide: false,
    };
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(unrelated)
        .assume_proposition(selected.clone());
    let derivation = assumptions
        .derive_atomic_proposition(&target)
        .expect("the selected range should establish the element access");

    assert!(derivation.check(&assumptions));
    assert_eq!(derivation.context_premises(), vec![selected]);
}

#[test]
fn loadable_symbolic_subrange_proves_an_indexed_cell() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let split = Bitvector32Term::Variable(Variable(87));
    let index = Bitvector32Term::Variable(Variable(88));
    let len = Bitvector32Term::Variable(Variable(89));
    let range = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.offset_by_int32_elements(split.clone()),
        bytes: Bitvector32Term::multiply(
            Bitvector32Term::subtract(len.clone(), split.clone()),
            Bitvector32Term::Constant(4),
        ),
        wide: false,
    };
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(index.clone()),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    // Reading `[split..len]` as its element count needs that count to be a
    // valid byte extent once scaled by four; a stated range carries this.
    let count = Bitvector32Term::subtract(len.clone(), split.clone());
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
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), count.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(
                count,
                Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(4)),
            ),
            true,
        );

    assert!(
        assumptions.derive_atomic_proposition(&target).is_some(),
        "split <= index < len should select a cell from [split..len]"
    );
}

#[test]
fn adjacent_loadable_regions_certify_their_concatenation() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let prefix = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(8),
        wide: false,
    };
    let next_cell = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let goal = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(12),
        wide: false,
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(prefix.clone())
        .assume_proposition(next_cell.clone());
    let derivation = assumptions
        .derive_atomic_proposition(&goal)
        .expect("an initialized next cell should extend the viewable prefix");
    assert!(derivation.check(&assumptions));
    let premises = derivation.context_premises();
    assert_eq!(premises.len(), 2);
    assert!(premises.contains(&prefix));
    assert!(premises.contains(&next_cell));

    let stored_memory = CMemory::new().store(
        data.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        CValue::Int32(Bitvector32Term::Constant(9)),
    );
    let stored_goal = Proposition::CMemoryLoadable {
        memory: stored_memory,
        base: data.clone(),
        bytes: Bitvector32Term::Constant(12),
        wide: false,
    };
    let stored_assumptions = PureFactContext::new().assume_proposition(prefix.clone());
    let stored_derivation = stored_assumptions
        .derive_atomic_proposition(&stored_goal)
        .expect("a materialized next cell should extend the viewable prefix");
    assert!(stored_derivation.check(&stored_assumptions));
    assert_eq!(stored_derivation.context_premises(), vec![prefix]);

    let gap = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(4)),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(goal.clone())
        .assume_proposition(gap);
    let too_wide = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: data,
        bytes: Bitvector32Term::Constant(16),
        wide: false,
    };
    assert!(!assumptions.proves(&too_wide));
}

#[test]
fn field_derived_capacity_range_covers_a_shorter_live_prefix() {
    let entry_memory = CMemory::new();
    let owner = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
            byte_width: 4,
        },
    };
    let field = |byte_offset| Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::Add(
            Box::new(owner.offset.clone()),
            Box::new(PointerOffsetTerm::Constant(byte_offset)),
        ),
    };
    let len = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&entry_memory),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let after_len = entry_memory
        .clone()
        .store(owner.clone(), CValue::Int32(len.clone()));
    let cap = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_len),
        Box::new(field(4)),
        crate::kernel::LoadKind::Bits32,
    );
    let after_cap = after_len
        .clone()
        .store(field(4), CValue::Int32(cap.clone()));
    let range_data_offset = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_cap),
        Box::new(field(8)),
        crate::kernel::LoadKind::Bits32,
    );
    let range_data = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(range_data_offset),
            byte_width: 4,
        },
    };
    let entry_data_offset = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&entry_memory),
        Box::new(field(8)),
        crate::kernel::LoadKind::Bits32,
    );
    let entry_data = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(entry_data_offset),
            byte_width: 4,
        },
    };
    let index = Bitvector32Term::Variable(Variable(2_000_000));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: after_cap,
            base: range_data,
            bytes: Bitvector32Term::multiply(cap.clone(), Bitvector32Term::Constant(4)),
            wide: false,
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), len.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(len, cap.clone()), true)
        // The capacity range is read as `cap` elements, so `cap` has to be a
        // count whose four-byte extent does not wrap; the clause that states
        // the range carries this.
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), cap.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(
                cap,
                Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(4)),
            ),
            true,
        );
    let target = Proposition::CMemoryLoadable {
        memory: entry_memory,
        base: entry_data.offset_by_int32_elements(index),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };

    assert!(
        assumptions.derive_atomic_proposition(&target).is_some(),
        "a field-derived capacity range must cover an entry-written live-prefix cell"
    );
}

#[test]
fn quantified_int32_fact_does_not_certify_an_instantiated_load() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact_index = Variable(2_100_000);
    let target_index = Variable(2_100_001);
    let length = Bitvector32Term::Variable(Variable(2_100_002));
    let indexed_fact_pointer = data.offset_by_int32_elements(Bitvector32Term::Variable(fact_index));
    let loaded_value = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&memory),
        Box::new(indexed_fact_pointer),
        crate::kernel::LoadKind::Bits32,
    );
    let guarded_fact = forall_int32(
        fact_index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Variable(fact_index),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(fact_index),
                        length.clone(),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(loaded_value, Bitvector32Term::Constant(7)),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(guarded_fact)
        .assume_condition(
            ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                Bitvector32Term::Variable(target_index),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(Bitvector32Term::Variable(target_index), length),
            true,
        );
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Variable(target_index)),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };

    assert!(
        !assumptions.proves(&target),
        "a logical value fact cannot grant viewability"
    );
    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(!assumptions.proves(&target));
    });
    assert!(
        !PureFactContext::new()
            .assume_proposition(forall_int32(
                fact_index,
                Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ))
            .proves(&target)
    );
}

#[test]
fn quantified_loadability_fact_certifies_an_instantiated_load() {
    let memory = CMemory::new().with_block("data", 16);
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact_index = Variable(2_100_020);
    let target_index = Variable(2_100_021);
    let length = Bitvector32Term::Variable(Variable(2_100_022));
    let guard_for = |index| {
        Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Variable(index),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(Bitvector32Term::Variable(index), length.clone()),
                true,
            )),
        )
    };
    let guarded_fact = forall_int32(
        fact_index,
        Proposition::Implies(
            Box::new(guard_for(fact_index)),
            Box::new(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: data.offset_by_int32_elements(Bitvector32Term::Variable(fact_index)),
                bytes: Bitvector32Term::Constant(4),
                wide: false,
            }),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(guarded_fact)
        .assume_proposition(guard_for(target_index));

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Variable(target_index)),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    }));
}

#[test]
fn quantified_signed_condition_fact_certifies_a_symbolic_index() {
    let fact_index = Variable(2_110_000);
    let target_index = Variable(2_110_001);
    let length = Bitvector32Term::Variable(Variable(2_110_002));
    let guard = |index: Variable| {
        Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Variable(index),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(Bitvector32Term::Variable(index), length.clone()),
                true,
            )),
        )
    };
    let fact = forall_int32(
        fact_index,
        Proposition::Implies(
            Box::new(guard(fact_index)),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Variable(fact_index),
                    Bitvector32Term::Constant(1),
                ),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(fact.clone())
        .assume_proposition(guard(target_index));
    let target = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Variable(target_index),
            Bitvector32Term::Constant(1),
        ),
        true,
    );

    let derivation = assumptions
        .derive_simp_proposition(&target)
        .expect("a universal with symbolic bounds should specialize at the target index");
    let (selected, argument, guards) = derivation
        .forall_int32_instantiation()
        .expect("the specialization should retain its universal evidence");
    assert_eq!(selected, &fact);
    assert_eq!(argument, &Bitvector32Term::Variable(target_index));
    assert_eq!(guards.len(), 2);
    assert!(derivation.check(&assumptions));
}

#[test]
fn quantified_atomic_derivation_retains_its_specialization_and_guards() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "typed-quantified-data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let index = Variable(2_100_100);
    let exit = Bitvector32Term::Variable(Variable(2_100_101));
    let indexed_load = |value| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(data.offset_by_int32_elements(value)),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let quantified = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Variable(index),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(Bitvector32Term::Variable(index), exit.clone()),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    indexed_load(Bitvector32Term::Variable(index)),
                    Bitvector32Term::Variable(index),
                ),
                true,
            )),
        ),
    );
    // The instantiation guard is stated exactly. Package 15 narrowed the
    // `ForallInt32Instantiation` rule to guards that are builtin solvable or
    // exactly available, because the evidence must name the premises it
    // consumed and the frozen condition checker does not report its own. The
    // `exit_guard_needing_a_derivation` case below pins that narrowing.
    let exit_guard = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(2), exit.clone()),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(
            indexed_load(Bitvector32Term::Constant(2)),
            Bitvector32Term::Constant(2),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(quantified.clone())
        .assume_proposition(exit_guard.clone());

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the selected universal instance should prove the concrete cell");
    let (selected, argument, guards) = derivation
        .forall_int32_instantiation()
        .expect("the atomic decision should retain its specialization");
    assert_eq!(selected, &quantified);
    assert_eq!(argument, &Bitvector32Term::Constant(2));
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
    let memory = CMemory::new();
    let data = Pointer {
        block: "refused-guard-data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let index = Variable(2_100_400);
    let exit = Bitvector32Term::Variable(Variable(2_100_401));
    let indexed_load = |value| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(data.offset_by_int32_elements(value)),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let quantified = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(Bitvector32Term::Variable(index), exit.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    indexed_load(Bitvector32Term::Variable(index)),
                    Bitvector32Term::Variable(index),
                ),
                true,
            )),
        ),
    );
    // `not (exit < 3)` entails `2 < exit`, but not exactly.
    let derivable_guard_source = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(exit, Bitvector32Term::Constant(3)),
        false,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(
            indexed_load(Bitvector32Term::Constant(2)),
            Bitvector32Term::Constant(2),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(quantified)
        .assume_proposition(derivable_guard_source);

    let retained = assumptions
        .derive_simp_proposition(&goal)
        .and_then(|derivation| derivation.forall_int32_instantiation().map(|_| ()));
    assert!(
        retained.is_none(),
        "an instantiation guard that needs a derivation must not be retained \
         as evidence whose premise list cannot name what discharged it"
    );
}

#[test]
fn quantified_int32_fact_certifies_a_concrete_indexed_load() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let index = Variable(2_100_003);
    let index_term = Bitvector32Term::Variable(index);
    let indexed_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&memory),
        Box::new(data.offset_by_int32_elements(index_term.clone())),
        crate::kernel::LoadKind::Bits32,
    );
    let guarded_fact = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        index_term.clone(),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        index_term.clone(),
                        Bitvector32Term::Constant(3),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(indexed_load, index_term),
                true,
            )),
        ),
    );
    let concrete_index = Bitvector32Term::Constant(1);
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(&memory),
                Box::new(data.offset_by_int32_elements(concrete_index.clone())),
                crate::kernel::LoadKind::Bits32,
            ),
            concrete_index,
        ),
        true,
    );

    assert!(
        PureFactContext::new()
            .assume_proposition(guarded_fact)
            .proves(&target)
    );
}

#[test]
fn quantified_copy_fact_certifies_concrete_pointer_indices() {
    let memory = CMemory::new();
    let destination = Pointer {
        block: "argument-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(2_200_000)), 4),
    };
    let source = Pointer {
        block: "argument-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(2_200_001)), 4),
    };
    let index = Variable(2_200_002);
    let index_term = Bitvector32Term::Variable(index);
    let load = |base: &Pointer, index: Bitvector32Term| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(base.offset_by_int32_elements(index)),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let copied = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        index_term.clone(),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        index_term.clone(),
                        Bitvector32Term::Constant(3),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
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
        let index = Bitvector32Term::Constant(index);
        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::equal(load(&destination, index.clone()), load(&source, index),),
            true,
        )));
    }
}

#[test]
fn quantified_int32_fact_does_not_certify_its_complete_guarded_range() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let index = Variable(2_100_010);
    let length = Bitvector32Term::Variable(Variable(2_100_011));
    let index_bits = Bitvector32Term::Variable(index);
    let loaded_value = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&memory),
        Box::new(data.offset_by_int32_elements(index_bits.clone())),
        crate::kernel::LoadKind::Bits32,
    );
    let guarded_fact = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        index_bits.clone(),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(index_bits, length.clone()),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(loaded_value, Bitvector32Term::Constant(7)),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new().assume_proposition(guarded_fact);
    let target = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::multiply(length.clone(), Bitvector32Term::Constant(4)),
        wide: false,
    };

    assert!(
        !assumptions.proves(&target),
        "a logical value fact cannot grant viewability"
    );
    assert!(!assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.with_block("other-state", 4),
        base: data.clone(),
        bytes: Bitvector32Term::multiply(length.clone(), Bitvector32Term::Constant(4)),
        wide: false,
    }));
    assert!(!assumptions.proves(&Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: "other-data".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        bytes: Bitvector32Term::multiply(length, Bitvector32Term::Constant(4)),
        wide: false,
    }));
}

#[test]
fn proposition_derivation_check_requires_its_context() {
    let x = Bitvector32Term::Variable(Variable(86));
    let proposition = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x, Bitvector32Term::Constant(0)),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(proposition.clone());
    let derivation = assumptions
        .derive_simp_proposition(&proposition)
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
    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
        arguments: vec![Term::Bitvector32(Bitvector32Term::Variable(variable))],
    };
    let goal = forall_int32(variable, body.clone());
    let assumptions = PureFactContext::new().assume_proposition(body);

    assert!(!assumptions.proves(&goal));
    assert!(assumptions.derive_proposition(&goal).is_none());
}

#[test]
fn forall_derivation_check_shadows_ambient_uses_of_the_binder_id() {
    let variable = Variable(187);
    let value = Bitvector32Term::Variable(variable);
    let goal = forall_int32(
        variable,
        Proposition::ConditionIs(ConditionTerm::equal(value.clone(), value), true),
    );
    let derivation = PureFactContext::new()
        .derive_proposition(&goal)
        .expect("reflexivity should prove a universal in an empty context");
    let contaminated = PureFactContext::new().assume_proposition(Proposition::Predicate {
        name: "ambient".to_string(),
        arguments: vec![Term::Bitvector32(Bitvector32Term::Variable(variable))],
    });

    assert!(derivation.check(&PureFactContext::new()));
    assert!(derivation.check(&contaminated));
}

#[test]
fn forall_introduction_keeps_outer_facts_when_the_body_ignores_the_binder() {
    let bound = Bitvector32Term::Variable(Variable(188));
    let left = Bitvector32Term::Variable(Variable(189));
    let middle = Bitvector32Term::Variable(Variable(190));
    let right = Bitvector32Term::Variable(Variable(191));
    let equality = |a, b| Proposition::ConditionIs(ConditionTerm::equal(a, b), true);
    let goal = forall_int32(Variable(188), equality(left.clone(), right.clone()));
    let first = equality(left.clone(), middle.clone());
    let second = equality(middle, right);
    let outer = equality(bound, left);
    let assumptions = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second.clone())
        .assume_proposition(outer.clone());

    let derivation = assumptions
        .derive_proposition(&goal)
        .expect("the binder-free body can use outer facts without weakening the context");
    assert!(derivation.check(&assumptions));
    assert_eq!(derivation.context_premises(), vec![outer, first, second]);
}

#[test]
fn singleton_substitution_derivation_records_only_its_bound_premises() {
    let variable = Variable(87);
    let value = Bitvector32Term::Variable(variable);
    let lower = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(3), value.clone()),
        true,
    );
    let upper = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(3)),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(value, Bitvector32Term::Constant(3)),
        true,
    );
    let unrelated = Proposition::Predicate {
        name: "unrelated".to_string(),
        arguments: vec![],
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(lower.clone())
        .assume_proposition(upper.clone())
        .assume_proposition(unrelated);
    let derivation = assumptions
        .derive_simp_proposition(&goal)
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
                    assumptions.derive_by_singleton_substitution(&goal, true),
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
    let index = Bitvector32Term::Variable(Variable(88));
    let upper = Bitvector32Term::Variable(Variable(89));
    let upper_bound =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(index.clone(), upper), true);
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            index.clone(),
            Bitvector32Term::add(index.clone(), Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let unrelated_order = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::Variable(Variable(90)),
            Bitvector32Term::Constant(0),
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
    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("an int32 value below another int32 value cannot overflow when incremented");

    assert!(derivation.check(&assumptions));
    assert_eq!(derivation.context_premises(), vec![upper_bound]);
}

#[test]
fn upper_bound_extends_to_a_nonoverflowing_successor() {
    let length = Bitvector32Term::Variable(Variable(89_100));
    let capacity = Bitvector32Term::Variable(Variable(89_101));
    let successor = Bitvector32Term::add(capacity.clone(), Bitvector32Term::Constant(1));
    let goal = ConditionTerm::signed_less_equal(length.clone(), successor.clone());
    let bounded = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(length, capacity.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(capacity.clone(), Bitvector32Term::Constant(100)),
            true,
        );

    assert_eq!(
        bounded.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Variable(Variable(89_100)),
            capacity.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        bounded.decide(&ConditionTerm::signed_add_overflows(
            capacity.clone(),
            Bitvector32Term::Constant(1),
        )),
        Some(false)
    );
    assert_eq!(bounded.decide(&goal), Some(true));
    assert_eq!(
        PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Variable(Variable(89_100)),
                    capacity,
                ),
                true,
            )
            .decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Variable(Variable(89_100)),
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
fn unsigned_extent_bound_below_the_sign_bit_is_decided_by_signed_order() {
    let count = Bitvector32Term::Variable(Variable(89_200));
    let end = Bitvector32Term::Variable(Variable(89_201));
    let limit = Bitvector32Term::Constant(1_073_741_823);
    let fits = ConditionTerm::unsigned_less_equal(count.clone(), limit.clone());
    let nonnegative = ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), count.clone());
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
        ConditionTerm::signed_less_than(count.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    assert_eq!(negative.decide(&fits), Some(false));

    let above = PureFactContext::new()
        .assume_condition(nonnegative, true)
        .assume_condition(ConditionTerm::signed_less_than(limit, count.clone()), true);
    assert_eq!(above.decide(&fits), Some(false));
}

/// An unsigned chain `x <u n`, `n <=u 4` is the signed chain over the
/// sign-bit-flipped atoms, so it gives `x <u 4`, and with it the signed range
/// `0 <= x` and `x < 4` an index needs. It does not compose with a signed
/// bound on `n` (a negative `n` is a huge unsigned one), with no bound on
/// `n`, or through a wrapped `n - 1`.
#[test]
fn unsigned_order_chain_bounds_its_low_end_in_signed_order() {
    let x = Bitvector32Term::Variable(Variable(89_300));
    let n = Bitvector32Term::Variable(Variable(89_301));
    let four = Bitvector32Term::Constant(4);
    let zero = Bitvector32Term::Constant(0);
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
            Bitvector32Term::Constant(3)
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
                Bitvector32Term::Subtract(Box::new(n), Box::new(Bitvector32Term::Constant(1))),
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
    let j = Bitvector32Term::Variable(Variable(87));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            true,
        );
    let proposition = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j, Bitvector32Term::Constant(1)),
            true,
        )),
    );

    assert!(!assumptions.proves(&proposition));
    assert!(assumptions.derive_proposition(&proposition).is_none());
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
    let memory = CMemory::new();
    let indexed_load = |index| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::scale_int32(index, 4),
            }),
            crate::kernel::LoadKind::Bits32,
        )
    };
    let k = Variable(88);
    let k_bits = Bitvector32Term::Variable(k);
    let load_k = indexed_load(k_bits.clone());
    let load_0 = indexed_load(Bitvector32Term::Constant(0));
    let load_1 = indexed_load(Bitvector32Term::Constant(1));
    let load_2 = indexed_load(Bitvector32Term::Constant(2));
    let load_1_again = load_1.clone();
    let finite_order_fact = Proposition::ForAll {
        var: k,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(k_bits, Bitvector32Term::Constant(1)),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(load_k, load_1.clone()),
                true,
            )),
        )),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(finite_order_fact)
        .assume_condition(
            ConditionTerm::signed_less_equal(load_1, load_2.clone()),
            true,
        );

    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(load_0.clone(), load_2),
        true,
    );
    assert!(
        !assumptions.proves(&goal),
        "the quantified bound is not an order fact until it is instantiated"
    );

    // The condition fact an explicit `enumerate` instantiation contributes.
    let enumerated =
        assumptions.assume_condition(ConditionTerm::signed_less_equal(load_0, load_1_again), true);
    assert!(enumerated.proves(&goal));
}

/// A bound available only under a guarded implication needs the explicit
/// step that introduces it.
///
/// The guard is exactly available, so the old collection discharged it with
/// the general prover and harvested the conclusion as an order fact. The
/// theory now sees only `condition_facts`, and the conclusion joins the
/// transitive path once an explicit `intro`/`extract` step has added it.
#[test]
fn guarded_implication_bound_needs_an_explicit_extraction() {
    let a = Bitvector32Term::Variable(Variable(97_001));
    let b = Bitvector32Term::Variable(Variable(97_002));
    let c = Bitvector32Term::Variable(Variable(97_003));
    let guard = ConditionTerm::signed_less_than(
        Bitvector32Term::Variable(Variable(97_004)),
        Bitvector32Term::Constant(10),
    );
    let a_le_b =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(a.clone(), b.clone()), true);
    let assumptions = PureFactContext::new()
        .assume_condition(guard.clone(), true)
        .assume_proposition(Proposition::Implies(
            Box::new(Proposition::ConditionIs(guard, true)),
            Box::new(a_le_b.clone()),
        ))
        .assume_condition(ConditionTerm::signed_less_equal(b, c.clone()), true);

    let goal = Proposition::ConditionIs(ConditionTerm::signed_less_equal(a, c), true);
    assert!(
        !assumptions.proves(&goal),
        "a guarded bound is not an order fact until the proof extracts it"
    );
    assert!(assumptions.assume_proposition(a_le_b).proves(&goal));
}

/// The order query's work does not grow with unrelated ambient propositions.
///
/// The removed collection walked every `prop_facts` entry and ran the prover
/// on each implication antecedent, so unrelated propositions were charged to
/// every order decision.
#[test]
fn order_path_decision_scales_flat_in_unrelated_propositions() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let a = Bitvector32Term::Variable(Variable(97_101));
            let b = Bitvector32Term::Variable(Variable(97_102));
            let c = Bitvector32Term::Variable(Variable(97_103));
            let mut assumptions = PureFactContext::new()
                .assume_condition(ConditionTerm::signed_less_equal(a.clone(), b.clone()), true)
                .assume_condition(ConditionTerm::signed_less_equal(b, c.clone()), true);
            for index in 0..size {
                let guard = ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(97_200 + index as u64)),
                    Bitvector32Term::Constant(10),
                );
                assumptions = assumptions
                    .assume_condition(guard.clone(), true)
                    .assume_proposition(Proposition::Implies(
                        Box::new(Proposition::ConditionIs(guard, true)),
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::signed_less_equal(
                                Bitvector32Term::Variable(Variable(97_400 + index as u64)),
                                Bitvector32Term::Variable(Variable(97_600 + index as u64)),
                            ),
                            true,
                        )),
                    ));
            }
            let goal = Proposition::ConditionIs(ConditionTerm::signed_less_equal(a, c), true);
            let (proved, work) =
                crate::instrumentation::measure_deterministic_work(|| assumptions.proves(&goal));
            assert!(proved);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "order decision grew with unrelated propositions: {samples:?}"
        );
    }
}

#[test]
fn conditional_forall_instantiates_at_same_named_variable_in_order_path() {
    let k = Variable(188);
    let k_bits = Bitvector32Term::Variable(k);
    let j = Bitvector32Term::Variable(Variable(189));
    let value_at_k = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(CMemory::new()),
        Box::new(Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::scale_int32(k_bits.clone(), 4),
        }),
        crate::kernel::LoadKind::Bits32,
    );
    let pivot = Bitvector32Term::Variable(Variable(191));
    let successor = Bitvector32Term::Variable(Variable(192));
    let induction_hypothesis = Proposition::ForAll {
        var: k,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(k_bits.clone(), j.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(value_at_k.clone(), pivot.clone()),
                true,
            )),
        )),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(induction_hypothesis)
        .assume_condition(
            ConditionTerm::signed_less_than(
                k_bits.clone(),
                Bitvector32Term::add(j.clone(), Bitvector32Term::Constant(1)),
            ),
            true,
        )
        .assume_condition(ConditionTerm::equal(k_bits, j.clone()), false)
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j, Bitvector32Term::Constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(pivot, successor.clone()),
            true,
        );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value_at_k, successor),
        true,
    );

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("quantified order instance should produce a simplifier derivation");
    assert_eq!(derivation.conclusion(), &goal);
    assert!(derivation.check(&assumptions));
}

#[test]
fn forall_int32_application_preserves_exact_premises_and_conclusion() {
    let binder = Variable(500);
    let bound = Bitvector32Term::Variable(binder);
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(bound.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::equal(bound.clone(), bound), true);
    let quantified = Proposition::ForAll {
        var: binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(premise),
            Box::new(conclusion),
        )),
    };
    let value = Bitvector32Term::Variable(Variable(501));
    let instantiated_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let instantiated_conclusion =
        Proposition::ConditionIs(ConditionTerm::equal(value.clone(), value), true);

    let theorem = prove_forall_int32_application(
        &quantified,
        Bitvector32Term::Variable(Variable(501)),
        std::slice::from_ref(&instantiated_premise),
    )
    .expect("exact int32 application should be certified");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(quantified),
            Box::new(Proposition::Implies(
                Box::new(instantiated_premise),
                Box::new(instantiated_conclusion),
            )),
        )
    );
}

#[test]
fn forall_int32_application_rejects_a_mismatched_premise() {
    let binder = Variable(510);
    let bound = Bitvector32Term::Variable(binder);
    let quantified = Proposition::ForAll {
        var: binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(bound.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(bound.clone(), bound),
                true,
            )),
        )),
    };
    let wrong = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::Variable(Variable(511)),
            Bitvector32Term::Constant(1),
        ),
        true,
    );

    assert!(
        prove_forall_int32_application(
            &quantified,
            Bitvector32Term::Variable(Variable(511)),
            &[wrong],
        )
        .is_none()
    );
}

#[test]
fn forall_int32_application_avoids_capturing_the_argument_variable() {
    let outer = Variable(520);
    let inner = Variable(521);
    let quantified = Proposition::ForAll {
        var: outer,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ForAll {
            var: inner,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(outer),
                    Bitvector32Term::Variable(inner),
                ),
                true,
            )),
        }),
    };
    let theorem =
        prove_forall_int32_application(&quantified, Bitvector32Term::Variable(inner), &[])
            .expect("capture-avoiding instantiation should be certified");
    let Proposition::Implies(_, conclusion) = theorem.proposition() else {
        panic!("application theorem should retain its quantified premise");
    };
    let Proposition::ForAll {
        var: renamed, body, ..
    } = conclusion.as_ref()
    else {
        panic!("nested quantifier should remain in the conclusion");
    };
    assert_ne!(*renamed, inner, "the inner binder must be renamed");
    assert!(matches!(
        body.as_ref(),
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(left, right),
            true
        ) if left.as_ref() == &Bitvector32Term::Variable(inner)
            && right.as_ref() == &Bitvector32Term::Variable(*renamed)
    ));
}

#[test]
fn forall_integer_application_preserves_exact_guard_and_wide_argument() {
    let binder = Variable(600);
    let bound = IntegerTerm::var(binder);
    let premise = Proposition::ConditionIs(
        ConditionTerm::IntegerGreaterEqual(
            bound.clone().into(),
            IntegerTerm::constant_i64(0).into(),
        ),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(bound.clone().into(), bound.clone().into()),
        true,
    );
    let quantified = Proposition::ForAll {
        var: binder,
        sort: Sort::Integer,
        body: Box::new(Proposition::Implies(
            Box::new(premise),
            Box::new(conclusion),
        )),
    };
    let wide = IntegerTerm::parse_constant("340282366920938463463374607431768211457")
        .expect("wide integer constant");
    let instantiated_premise = Proposition::ConditionIs(
        ConditionTerm::IntegerGreaterEqual(
            wide.clone().into(),
            IntegerTerm::constant_i64(0).into(),
        ),
        true,
    );
    let instantiated_conclusion = Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(wide.clone().into(), wide.into()),
        true,
    );
    let theorem = prove_forall_integer_application(
        &quantified,
        IntegerTerm::parse_constant("340282366920938463463374607431768211457").unwrap(),
        std::slice::from_ref(&instantiated_premise),
    )
    .expect("wide mathematical integer application should be certified");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(quantified),
            Box::new(Proposition::Implies(
                Box::new(instantiated_premise),
                Box::new(instantiated_conclusion),
            )),
        )
    );
}

#[test]
fn forall_integer_application_rejects_wrong_or_changed_guards() {
    let binder = Variable(610);
    let bound = IntegerTerm::var(binder);
    let guard = Proposition::ConditionIs(
        ConditionTerm::IntegerGreaterEqual(
            bound.clone().into(),
            IntegerTerm::constant_i64(0).into(),
        ),
        true,
    );
    let quantified = Proposition::ForAll {
        var: binder,
        sort: Sort::Integer,
        body: Box::new(Proposition::Implies(
            Box::new(guard),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(bound.clone().into(), bound.into()),
                true,
            )),
        )),
    };
    let value = IntegerTerm::constant_i64(4);
    let changed = Proposition::ConditionIs(
        ConditionTerm::IntegerGreaterEqual(
            value.clone().into(),
            IntegerTerm::constant_i64(1).into(),
        ),
        true,
    );
    assert!(prove_forall_integer_application(&quantified, value.clone(), &[]).is_none());
    assert!(prove_forall_integer_application(&quantified, value, &[changed]).is_none());

    let wrong_sort = Proposition::ForAll {
        var: binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                IntegerTerm::var(binder).into(),
                IntegerTerm::constant_i64(0).into(),
            ),
            true,
        )),
    };
    assert!(
        prove_forall_integer_application(&wrong_sort, IntegerTerm::constant_i64(4), &[]).is_none()
    );
}

#[test]
fn forall_integer_application_renames_nested_forall_and_exists_once() {
    let outer = Variable(620);
    let repeated = Variable(621);
    let body = Proposition::ForAll {
        var: repeated,
        sort: Sort::Integer,
        body: Box::new(Proposition::Exists {
            name: "repeated".into(),
            var: repeated,
            sort: Sort::Integer,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(
                    IntegerTerm::var(outer).into(),
                    IntegerTerm::var(repeated).into(),
                ),
                true,
            )),
        }),
    };
    let quantified = Proposition::ForAll {
        var: outer,
        sort: Sort::Integer,
        body: Box::new(body),
    };
    let theorem = prove_forall_integer_application(&quantified, IntegerTerm::var(repeated), &[])
        .expect("capture-avoiding integer application should be certified");
    let Proposition::Implies(_, conclusion) = theorem.proposition() else {
        panic!("application theorem should retain its quantified premise");
    };
    let Proposition::ForAll {
        var: renamed_forall,
        body,
        ..
    } = conclusion.as_ref()
    else {
        panic!("nested forall should remain in the conclusion");
    };
    let Proposition::Exists {
        var: renamed_exists,
        body,
        ..
    } = body.as_ref()
    else {
        panic!("nested exists should remain in the conclusion");
    };
    assert_ne!(*renamed_forall, repeated);
    assert_ne!(*renamed_exists, repeated);
    assert_ne!(*renamed_forall, *renamed_exists);
    assert!(matches!(
        body.as_ref(),
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true)
            if left.as_ref() == &IntegerTerm::var(repeated)
                && right.as_ref() == &IntegerTerm::var(*renamed_exists)
    ));
}

#[test]
fn forall_integer_application_supports_nested_machine_sorts_and_rejects_unsupported_carriers() {
    let binder = Variable(630);
    let unsupported = Proposition::ForAll {
        var: binder,
        sort: Sort::Integer,
        body: Box::new(Proposition::Predicate {
            name: "unsupported_integer_application".into(),
            arguments: vec![],
        }),
    };
    assert!(
        prove_forall_integer_application(&unsupported, IntegerTerm::constant_i64(1), &[]).is_none()
    );
    let nested_machine_sort = Proposition::ForAll {
        var: binder,
        sort: Sort::Integer,
        body: Box::new(Proposition::ForAll {
            var: Variable(631),
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(
                    IntegerTerm::var(binder).into(),
                    IntegerTerm::constant_i64(0).into(),
                ),
                true,
            )),
        }),
    };
    assert!(
        prove_forall_integer_application(&nested_machine_sort, IntegerTerm::constant_i64(1), &[])
            .is_some()
    );

    let true_body = Proposition::ForAll {
        var: binder,
        sort: Sort::Integer,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::Constant(true),
            true,
        )),
    };
    assert!(
        prove_forall_integer_application(&true_body, IntegerTerm::constant_i64(1), &[]).is_some()
    );
}

#[test]
fn forall_integer_application_emits_no_theorem_after_work_exhaustion() {
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
        let theorem =
            prove_forall_integer_application(&quantified, IntegerTerm::constant_i64(7), &[]);
        crate::instrumentation::emit(crate::instrumentation::VerificationEvent::TacticFinished {
            tactic,
            elapsed: std::time::Duration::ZERO,
            work: 0,
        });
        assert!(theorem.is_none(), "work exhaustion must not emit a theorem");
    });
}

fn nested_integer_forall(depth: usize, capture: bool) -> Proposition {
    let outer = Variable(700);
    let mut body = Proposition::ConditionIs(
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
        body = Proposition::ForAll {
            var,
            sort: Sort::Integer,
            body: Box::new(body),
        };
    }
    Proposition::ForAll {
        var: outer,
        sort: Sort::Integer,
        body: Box::new(body),
    }
}

#[test]
fn forall_integer_application_work_is_linear_in_nested_binders() {
    std::thread::Builder::new()
        .name("integer-quantifier-scaling".into())
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            for capture in [false, true] {
                let mut measurements = Vec::new();
                for depth in [16, 32, 64, 128] {
                    let quantified = nested_integer_forall(depth, capture);
                    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                        prove_forall_integer_application(
                            &quantified,
                            if capture {
                                IntegerTerm::var(Variable(701))
                            } else {
                                IntegerTerm::constant_i64(7)
                            },
                            &[],
                        )
                        .expect("nested Integer application")
                    });
                    measurements.push(work);
                }
                for pair in measurements.windows(2) {
                    assert!(
                        pair[1] <= pair[0] * 3 + 32,
                        "capture={capture}: {measurements:?}"
                    );
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn forall_integer_application_preserves_repeated_squaring_as_a_shared_expression() {
    let binder = Variable(750);
    let mut measurements = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut term = IntegerTerm::var(binder);
        for _ in 0..depth {
            let child: SharedIntegerTerm = term.into();
            term = IntegerTerm::Multiply(child.clone(), child);
        }
        let quantified = Proposition::ForAll {
            var: binder,
            sort: Sort::Integer,
            body: Box::new(Proposition::Equal(
                Term::Integer(term),
                Term::Integer(IntegerTerm::constant_i64(0)),
            )),
        };
        let (theorem, work) = crate::instrumentation::measure_deterministic_work(|| {
            prove_forall_integer_application(&quantified, IntegerTerm::constant_i64(2), &[])
                .expect("structural instantiation remains bounded")
        });
        let Proposition::Implies(_, body) = theorem.proposition() else {
            panic!("application")
        };
        let Proposition::Equal(Term::Integer(term), _) = body.as_ref() else {
            panic!("equality")
        };
        let mut current = term;
        for _ in 0..depth {
            let IntegerTerm::Multiply(left, right) = current else {
                panic!("instantiation must not evaluate repeated squares")
            };
            assert_eq!(left.id(), right.id(), "substitution preserves sharing");
            current = left.as_ref();
        }
        assert_eq!(current, &IntegerTerm::constant_i64(2));
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{measurements:?}");
    }
}

#[test]
fn forall_integer_application_charges_shared_replacement_only_once() {
    let binder = Variable(751);
    let mut measurements = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut replacement = IntegerTerm::var(Variable(752));
        let mut body = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        for _ in 0..size {
            let child: SharedIntegerTerm = replacement.into();
            replacement = IntegerTerm::Add(child.clone(), child);
            body = Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(binder)),
                    Term::Integer(IntegerTerm::constant_i64(0)),
                )),
                Box::new(body),
            );
        }
        let quantified = Proposition::ForAll {
            var: binder,
            sort: Sort::Integer,
            body: Box::new(body),
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            prove_forall_integer_application(&quantified, replacement, &[])
                .expect("shared replacement application")
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{measurements:?}");
    }
}

#[test]
fn simultaneous_proposition_substitution_does_not_rewrite_installed_values() {
    let first = Variable(540);
    let second = Variable(541);
    let proposition = Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(first),
                Bitvector32Term::Constant(5),
            ),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(first),
                Bitvector32Term::Variable(second),
            ),
            true,
        )),
    );
    let substitutions = BTreeMap::from([
        (first, Bitvector32Term::Variable(second)),
        (second, Bitvector32Term::Constant(0)),
    ]);

    let substituted = substitute_bitvector_variables_in_proposition(&proposition, &substitutions);
    assert_eq!(
        substituted,
        Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(second),
                    Bitvector32Term::Constant(5),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(second),
                    Bitvector32Term::Constant(0),
                ),
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
    let left = Proposition::ForAll {
        var: left_binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(free),
                Bitvector32Term::Constant(5),
            ),
            true,
        )),
    };
    let right = Proposition::ForAll {
        var: right_binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(free),
                Bitvector32Term::Constant(5),
            ),
            true,
        )),
    };

    assert!(!propositions_alpha_equivalent(&left, &right));
}

#[test]
fn range_fold_substitution_renames_a_captured_binder() {
    let source = Variable(560);
    let accumulator = Variable(561);
    let item = Variable(562);
    let fold = Bitvector32Term::range_fold(
        Bitvector32Term::Variable(Variable(563)),
        Bitvector32Term::Variable(Variable(564)),
        Bitvector32Term::Constant(0),
        accumulator,
        item,
        Bitvector32Term::add(
            Bitvector32Term::Variable(accumulator),
            Bitvector32Term::Variable(item),
        ),
    );
    let term = Bitvector32Term::add(Bitvector32Term::Variable(source), fold);

    let substituted =
        substitute_bitvector_variable(&term, source, &Bitvector32Term::Variable(item));
    let Bitvector32Term::Add(left, fold) = &substituted else {
        panic!("substitution should preserve the outer addition");
    };
    let Bitvector32Term::RangeFold {
        accumulator: renamed_accumulator,
        item: renamed_item,
        body,
        ..
    } = fold.as_ref()
    else {
        panic!("substitution should preserve the symbolic range fold");
    };
    assert_eq!(left.as_ref(), &Bitvector32Term::Variable(item));
    assert_ne!(*renamed_item, item);
    assert_eq!(*renamed_accumulator, accumulator);
    assert_eq!(
        body.as_ref(),
        &Bitvector32Term::add(
            Bitvector32Term::Variable(accumulator),
            Bitvector32Term::Variable(*renamed_item),
        )
    );
}

#[test]
fn assumptions_prove_by_bounded_disjunction_cases() {
    let x = Bitvector32Term::Variable(Variable(89));
    let x_is_zero = Proposition::ConditionIs(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let x_is_one = Proposition::ConditionIs(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Or(
        Box::new(x_is_zero.clone()),
        Box::new(x_is_one.clone()),
    ));

    // The general prover does not eliminate disjunctions; the explicit
    // derivation still does.
    let proposition = Proposition::Or(Box::new(x_is_one), Box::new(x_is_zero));
    assert!(!assumptions.proves(&proposition));
    assert_checkable_derivation(&assumptions, &proposition);
}

#[test]
fn known_memory_block_bounds_prove_symbolic_element_access() {
    let index = Variable(91);
    let index_bits = Bitvector32Term::Variable(index);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index_bits.clone(), Bitvector32Term::Constant(3)),
            true,
        );
    let memory = CMemory::new().with_block("local:a", 12);
    let pointer = CMemory::local_pointer("a").offset_by_int32_elements(index_bits);

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    }));
    assert!(assumptions.proves(&Proposition::CMemoryCanStore {
        memory,
        pointer,
        byte_width: 4,
    }));
}

#[test]
fn symbolic_int32_range_directly_proves_constant_element_loadable() {
    let memory = CMemory::new();
    let base = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let length = Bitvector32Term::Variable(Variable(89));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        // The range's element count has to be one whose four-byte extent does
        // not wrap before it can be read as `length` elements.
        .assume_condition(
            ConditionTerm::signed_less_equal(
                length.clone(),
                Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(4)),
            ),
            true,
        )
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::multiply(length, Bitvector32Term::Constant(4)),
            wide: false,
        });

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    }));
}

#[test]
fn assumptions_prove_forall_int32_array_range_body() {
    let index = Variable(90);
    let index_bits = Bitvector32Term::Variable(index);
    let memory = CMemory::new().with_block("block", 12);
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let indexed_pointer = base.offset_by_int32_elements(index_bits.clone());
    let in_segment = Proposition::And(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(index_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(index_bits, Bitvector32Term::Constant(3)),
            true,
        )),
    );
    let loadable_index = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: indexed_pointer,
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
        memory,
        base,
        bytes: Bitvector32Term::Constant(12),
        wide: false,
    });

    assert!(assumptions.proves(&forall_int32(
        index,
        Proposition::Implies(Box::new(in_segment), Box::new(loadable_index)),
    )));
}

#[test]
fn loadability_transports_to_snapshot_with_symbolic_index_bounds() {
    let index = Bitvector32Term::Variable(Variable(190));
    let cursor = Bitvector32Term::Variable(Variable(191));
    let range_memory = CMemory::new();
    let snapshot_memory = CMemory::new().with_block("local:j", 4);
    let base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: range_memory,
            base: base.clone(),
            bytes: Bitvector32Term::Constant(12),
            wide: false,
        })
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), cursor.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(cursor.clone(), Bitvector32Term::Constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(cursor, Bitvector32Term::Constant(2)),
            false,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            index.clone(),
            Bitvector32Term::Constant(3),
        )),
        Some(true)
    );
    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: snapshot_memory,
        base: base.offset_by_int32_elements(index),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    }));
}

#[test]
fn loadability_same_base_extent_uses_graph_for_byte_count() {
    let before = CMemory::new().with_block("effect-side", 4);
    let written = Pointer {
        block: "effect-side".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let after = before
        .clone()
        .store(written.clone(), int32(Bitvector32Term::Constant(7)));
    let base = Pointer::symbolic(Variable(90_301));
    let a = Bitvector32Term::Variable(Variable(90_302));
    let b = Bitvector32Term::Variable(Variable(90_303));
    let bytes = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
    let fact = Proposition::CMemoryLoadable {
        memory: before.clone(),
        base: base.clone(),
        bytes: bytes(a.clone()),
        wide: false,
    };
    let goal = Proposition::CMemoryLoadable {
        memory: after.clone(),
        base: base.clone(),
        bytes: bytes(b.clone()),
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
    let derivation = with_premise
        .derive_atomic_proposition(&goal)
        .expect("the same-base loadable range should transport");
    assert!(derivation.check(&with_premise));
    assert!(!without_premise.proves_atomic_without_search(&goal));
    let withdrawn =
        with_premise.without_exact_fact(&Proposition::ConditionIs(premise.clone(), true));
    assert!(!withdrawn.proves_atomic_without_search(&goal));
    let without_loadable = PureFactContext::new().assume_condition(premise, true);
    assert!(!without_loadable.proves_atomic_without_search(&goal));
    let other_base = Proposition::CMemoryLoadable {
        memory: after,
        base: Pointer::symbolic(Variable(90_304)),
        bytes: bytes(b),
        wide: false,
    };
    assert!(!with_premise.proves_atomic_without_search(&other_base));
}

#[test]
fn loadability_same_base_extent_graph_queries_scale_without_fact_index() {
    let memory = CMemory::new();
    let base = Pointer::symbolic(Variable(90_310));
    let var = |id| Bitvector32Term::Variable(Variable(id));
    let bytes = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
    for size in [16u64, 64, 256, 1024] {
        let fact = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: bytes(var(0)),
            wide: false,
        };
        let mut context = PureFactContext::new().assume_proposition(fact);
        for index in 0..size {
            context =
                context.assume_condition(ConditionTerm::equal(var(index), var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let goal = Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: base.clone(),
                    bytes: bytes(var(index)),
                    wide: false,
                };
                assert!(context.proves_atomic_without_search(&goal));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

/// `lower <= term and term < upper`.
fn int32_half_open_bound(term: &Bitvector32Term, lower: i64, upper: i64) -> Proposition {
    Proposition::And(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(term.clone(), signed_i64_bitvector_constant(lower)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
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
    let k_bits = Bitvector32Term::Variable(k);
    let guarded = Proposition::Implies(
        Box::new(int32_half_open_bound(&k_bits, 0, 3)),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
    );
    let bare = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(3)),
        true,
    );
    let body = Proposition::And(Box::new(guarded.clone()), Box::new(bare));

    assert!(finite_forall_ranges(&[k], &body).is_none());
    assert!(!PureFactContext::new().proves(&forall_int32(k, body)));
    // The guarded conjunct alone still derives by instantiation.
    assert!(PureFactContext::new().proves(&forall_int32(k, guarded)));
}

#[test]
fn finite_forall_instantiates_the_hull_of_every_guard() {
    // Two guards of different widths: the universal is vacuous only outside
    // the wider one, so instances must cover 0..=9, where `k < 5` fails at
    // k = 5 while `k < 10` holds throughout.
    let k = Variable(92_101);
    let k_bits = Bitvector32Term::Variable(k);
    let narrow = Proposition::Implies(
        Box::new(int32_half_open_bound(&k_bits, 0, 3)),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
    );
    let wide = |upper: u32| {
        Proposition::Implies(
            Box::new(int32_half_open_bound(&k_bits, 0, 10)),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(upper)),
                true,
            )),
        )
    };
    let false_at_five = Proposition::And(Box::new(narrow.clone()), Box::new(wide(5)));
    let ranges = finite_forall_ranges(&[k], &false_at_five).expect("both leaves are guarded");
    assert_eq!((ranges[0].lower, ranges[0].upper), (0, 9));
    assert!(!PureFactContext::new().proves(&forall_int32(k, false_at_five)));

    let true_throughout = Proposition::And(Box::new(narrow), Box::new(wide(10)));
    assert!(PureFactContext::new().proves(&forall_int32(k, true_throughout)));
}

#[test]
fn assumptions_prove_finite_forall_int32_by_instantiation() {
    let i = Variable(92);
    let j = Variable(93);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let antecedent = Proposition::And(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(j_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
        )),
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(i_bits.clone(), j_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(j_bits, Bitvector32Term::Constant(3)),
                true,
            )),
        )),
    );
    let consequent = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits, Bitvector32Term::Constant(1)),
            true,
        )),
    );

    assert!(PureFactContext::new().proves(&forall_int32(
        i,
        forall_int32(
            j,
            Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
        ),
    )));
}

#[test]
fn assumptions_use_finite_forall_fact_to_prove_condition() {
    let k = Variable(94);
    let base_left = Bitvector32Term::Variable(Variable(95));
    let base_right = Bitvector32Term::Variable(Variable(96));
    let k_bits = Bitvector32Term::Variable(k);
    let antecedent = Proposition::And(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(3)),
            true,
        )),
    );
    let consequent = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Add(Box::new(base_left.clone()), Box::new(k_bits.clone())),
            Bitvector32Term::Add(Box::new(base_right.clone()), Box::new(k_bits)),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(forall_int32(
        k,
        Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
    ));

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Add(Box::new(base_left), Box::new(Bitvector32Term::Constant(1))),
            Bitvector32Term::Add(Box::new(base_right), Box::new(Bitvector32Term::Constant(1))),
        ),
        true,
    )));
}

#[test]
fn order_solver_uses_negated_less_than_transitively() {
    let a = Bitvector32Term::Variable(Variable(94));
    let b = Bitvector32Term::Variable(Variable(95));
    let c = Bitvector32Term::Variable(Variable(96));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(b.clone(), a.clone()), false)
        .assume_condition(ConditionTerm::signed_less_than(c.clone(), b), false);

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(a, c),
        true,
    )));
}

#[test]
fn assumptions_do_not_prove_implication_by_treating_unknown_antecedent_as_false() {
    let x = Bitvector32Term::Variable(Variable(91));
    let antecedent = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let consequent =
        Proposition::ConditionIs(ConditionTerm::equal(x, Bitvector32Term::Constant(0)), true);

    assert!(!PureFactContext::new().proves(&Proposition::Implies(
        Box::new(antecedent),
        Box::new(consequent),
    )));
}

#[test]
fn assumptions_prove_implication_with_refuted_antecedent() {
    let x = Bitvector32Term::Variable(Variable(91));
    let condition = ConditionTerm::equal(x, Bitvector32Term::Constant(0));
    let assumptions = PureFactContext::new().assume_condition(condition.clone(), true);
    let antecedent = Proposition::ConditionIs(condition, false);
    let consequent = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(92)),
            Bitvector32Term::Constant(7),
        ),
        true,
    );

    assert!(assumptions.proves(&Proposition::Implies(
        Box::new(antecedent),
        Box::new(consequent),
    )));
}

#[test]
fn simp_derives_vacuous_implication_before_searching_large_consequent() {
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
        Bitvector32Term::Variable(Variable(93)),
        Bitvector32Term::Constant(0),
    );
    let antecedent = Proposition::ConditionIs(condition.clone(), true);
    let consequent = unknown_tree(9, 0);
    let goal = Proposition::Implies(Box::new(antecedent), Box::new(consequent));
    let assumptions = PureFactContext::new().assume_condition(condition, false);

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("a refuted antecedent should close before inspecting the consequent");
    assert!(derivation.check(&assumptions));
}

#[test]
fn simp_derives_implication_body_before_refuting_known_antecedent() {
    let antecedent_condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(94)),
        Bitvector32Term::Constant(0),
    );
    let consequent_condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(95)),
        Bitvector32Term::Constant(7),
    );
    let goal = Proposition::Implies(
        Box::new(Proposition::ConditionIs(antecedent_condition.clone(), true)),
        Box::new(Proposition::ConditionIs(consequent_condition.clone(), true)),
    );
    let assumptions = PureFactContext::new()
        .assume_condition(antecedent_condition, true)
        .assume_condition(consequent_condition, true);

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("a known antecedent should use the available consequent directly");
    assert!(derivation.check(&assumptions));
}

#[test]
fn assumptions_simplify_overflow_through_equality_chain() {
    let index = Bitvector32Term::Variable(Variable(91));
    let length = Bitvector32Term::Variable(Variable(92));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(index.clone(), length.clone()), true)
        .assume_condition(
            ConditionTerm::equal(length, Bitvector32Term::Constant(0)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            index,
            Bitvector32Term::Constant(1),
        )),
        Some(false),
    );
}

#[test]
fn same_block_pointer_equality_transports_through_equal_offsets() {
    let left = Pointer {
        block: "shared".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91)), 4),
    };
    let right = Pointer {
        block: "shared".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(left.clone(), right.clone()),
        true,
    );

    assert!(pointers_proven_equal_for_memory_resolution(
        &left.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &assumptions,
    ));
}

#[test]
fn symbolic_pointer_equality_needs_explicit_guarded_arithmetic() {
    let base = Bitvector32Term::Variable(Variable(100_000));
    let index = Bitvector32Term::Variable(Variable(1_000_000));
    let source_left = Pointer {
        block: PointerBlock::Symbolic(Variable(1_000_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let source_right = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::scale_int32(base.clone(), 4)),
            Box::new(PointerOffsetTerm::scale_int32(index.clone(), 4)),
        ),
    };
    let goal_left = source_left.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let goal_right = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::scale_int32(base, 4)),
            Box::new(PointerOffsetTerm::scale_int32(
                Bitvector32Term::add(index, Bitvector32Term::Constant(1)),
                4,
            )),
        ),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_equal(source_left, source_right),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_add_overflows(
                Bitvector32Term::Variable(Variable(1_000_000)),
                Bitvector32Term::Constant(1),
            ),
            false,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            Bitvector32Term::Variable(Variable(1_000_000)),
            Bitvector32Term::Constant(1),
        )),
        Some(false),
    );
    // The graph does not distribute a scaled int32 addition merely because
    // the ambient context can prove its no-overflow guard. A proof can name
    // the pointer relation and guard in `arithmetic() using` instead.
    assert_eq!(
        assumptions.decide(&ConditionTerm::pointer_equal(goal_left, goal_right)),
        None,
    );
}

#[test]
fn builtin_obligation_solver_discharges_concrete_invariant() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 4);
    let invariant = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer,
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let state = CState::new().with_local("x", int32(0)).with_memory(memory);
    let statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        vec![invariant],
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let theorem =
        prove_symbolic_c_execution(state.clone(), statement.clone(), PureFactContext::new())
            .expect("concrete invariant should be solved");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: Box::new(state.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Normal(Box::new(state)),
        }
    );
}

#[test]
fn equality_rewrites_through_matching_decrement() {
    let left = Bitvector32Term::Variable(Variable(66_001));
    let right = Bitvector32Term::Variable(Variable(66_002));
    let equality =
        Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right.clone()), true);
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::subtract(left, Bitvector32Term::Constant(1)),
            Bitvector32Term::subtract(right, Bitvector32Term::Constant(1)),
        ),
        true,
    );

    assert!(
        PureFactContext::new()
            .assume_proposition(equality)
            .derive_simp_proposition(&goal)
            .is_some()
    );
}

#[test]
fn symbolic_max_lt_branch_is_native_theorem() {
    let a = Variable(10);
    let b = Variable(11);
    let theorem = prove_c_max_lt_returns_right(a, b).expect("lt branch should prove");
    let condition = ConditionTerm::Bitvector32SignedLessThan(
        Box::new(Bitvector32Term::Variable(a)),
        Box::new(Bitvector32Term::Variable(b)),
    );
    let state = c_max_state(
        int32(Bitvector32Term::Variable(a)),
        int32(Bitvector32Term::Variable(b)),
    );

    assert_eq!(
        theorem.proposition(),
        &forall_int32(
            a,
            forall_int32(
                b,
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(condition, true)),
                    Box::new(Proposition::CStatementExecutes {
                        state: Box::new(state.clone()),
                        statement: Box::new(c_max_body()),
                        outcome: CStatementOutcome::Return {
                            value: int32(Bitvector32Term::Variable(b)),
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
    let theorem = prove_c_max_not_lt_returns_left(a, b).expect("false branch should prove");
    let condition = ConditionTerm::Bitvector32SignedLessThan(
        Box::new(Bitvector32Term::Variable(a)),
        Box::new(Bitvector32Term::Variable(b)),
    );
    let state = c_max_state(
        int32(Bitvector32Term::Variable(a)),
        int32(Bitvector32Term::Variable(b)),
    );

    assert_eq!(
        theorem.proposition(),
        &forall_int32(
            a,
            forall_int32(
                b,
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(condition, false)),
                    Box::new(Proposition::CStatementExecutes {
                        state: Box::new(state.clone()),
                        statement: Box::new(c_max_body()),
                        outcome: CStatementOutcome::Return {
                            value: int32(Bitvector32Term::Variable(a)),
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
    let left = Bitvector32Term::Variable(Variable(93_101));
    let right = Bitvector32Term::Variable(Variable(93_102));
    let assumptions =
        PureFactContext::new().assume_condition(ConditionTerm::signed_less_than(left, right), true);
    let _scope = assumptions.enter_id_scope();

    let first = assumptions.condition_order_facts();
    let second = assumptions.condition_order_facts();

    assert_eq!(first.len(), 1, "the order fact should be collected");
    assert!(
        std::rc::Rc::ptr_eq(&first, &second),
        "a repeated collection over one fact set should share the first scan"
    );
}

#[test]
fn repeated_resolution_queries_do_not_repay_their_search() {
    let left = Pointer {
        block: "memo-regression".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93_103)), 4),
    };
    let right = Pointer {
        block: "memo-regression".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93_104)), 4),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(
                Bitvector32Term::Variable(Variable(93_103)),
                Bitvector32Term::Variable(Variable(93_104)),
            ),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(memory_range(left.clone(), 0, 1))),
            right: Box::new(CResource::Memory(memory_range(right.clone(), 0, 1))),
        });
    let _scope = assumptions.enter_id_scope();

    let work_for = |index: usize, query: fn(&Pointer, &Pointer, &PureFactContext) -> bool| {
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
    let base = Pointer {
        block: "common-base".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93_105)), 4),
    };
    let field = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::add(base.offset.clone(), PointerOffsetTerm::Constant(4)),
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
    let block = PointerBlock::Symbolic(Variable(93_200));
    let element = |index: Bitvector32Term| Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let i = Bitvector32Term::Variable(Variable(93_201));
    let j = Bitvector32Term::Variable(Variable(93_202));
    let ordered = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(Box::new(i.clone()), Box::new(j.clone())),
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
    let first = Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block,
        offset: PointerOffsetTerm::Constant(4),
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

#[test]
fn consistent_order_context_scales_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(95_000 + index as u64)),
                        Bitvector32Term::Variable(Variable(96_000 + index as u64)),
                    ),
                    true,
                );
            }
            let (inconsistent, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.is_inconsistent()
            });
            assert!(!inconsistent, "unrelated order facts are consistent");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "consistent order contradiction scanning is superlinear: {samples:?}"
        );
    }
}

/// Pins the non-structural fallback in context inconsistency. Equality classes
/// decide structural endpoints, but `x + y` and `y + x` are related only by
/// additive theory equality, which is not an equality-graph edge, so this
/// contradiction is reachable only through the retained pairwise comparison.
#[test]
fn derived_order_contradiction_uses_theory_equal_endpoints() {
    let x = Bitvector32Term::Variable(Variable(97_001));
    let y = Bitvector32Term::Variable(Variable(97_002));
    let middle = Bitvector32Term::Variable(Variable(97_003));
    let left_sum = Bitvector32Term::add(x.clone(), y.clone());
    let right_sum = Bitvector32Term::add(y, x);
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

/// An order endpoint may resolve through any finite chain of context-equal
/// stored addresses. Contradiction indexing must follow the complete chain:
/// a depth cutoff can otherwise miss `load < middle < resolved(load)`.
#[test]
fn deep_contextual_load_order_contradiction_has_no_index_depth_cutoff() {
    fn contextual_load_chain(
        length: usize,
        terminal: Bitvector32Term,
    ) -> (Bitvector32Term, PureFactContext) {
        let mut next = terminal;
        let mut assumptions = PureFactContext::new();
        for index in (0..length).rev() {
            let stored_index = Bitvector32Term::Variable(Variable(98_000 + index as u64 * 2));
            let query_index = Bitvector32Term::Variable(Variable(98_001 + index as u64 * 2));
            let block = format!("deep-order-resolution-{index}");
            let stored_pointer = Pointer {
                block: block.clone().into(),
                offset: PointerOffsetTerm::scale_int32(stored_index.clone(), 4),
            };
            let query_pointer = Pointer {
                block: block.into(),
                offset: PointerOffsetTerm::scale_int32(query_index.clone(), 4),
            };
            crate::kernel::eval::declare_load_access_width(&query_pointer, 4);
            let memory = CMemory::new().store(stored_pointer, CValue::Int32(next));
            next = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory),
                Box::new(query_pointer),
                crate::kernel::LoadKind::Bits32,
            );
            assumptions =
                assumptions.assume_condition(ConditionTerm::equal(stored_index, query_index), true);
        }
        (next, assumptions)
    }

    let samples = [6usize, 8, 16, 32]
        .into_iter()
        .map(|length| {
            let terminal = Bitvector32Term::Variable(Variable(99_000));
            let middle = Bitvector32Term::Variable(Variable(99_001));
            let (load, assumptions) = contextual_load_chain(length, terminal.clone());
            let assumptions = assumptions
                .assume_condition(ConditionTerm::signed_less_than(load, middle.clone()), true)
                .assume_condition(
                    ConditionTerm::signed_less_than(middle.clone(), terminal.clone()),
                    true,
                );
            let (inconsistent, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.is_inconsistent()
            });
            assert!(
                inconsistent,
                "a contextual load chain of length {length} must close the strict cycle"
            );
            (length, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "deep endpoint contradiction indexing is superlinear: {samples:?}"
        );
    }
}

/// The issue-named fixed-arithmetic curve: one overflow decision whose
/// operands have exact bounds, while unrelated order facts grow. The interval
/// index answers from exact endpoint bounds, so the decision must not rescan
/// the growing context.
#[test]
fn fixed_overflow_decision_scales_near_linearly_with_unrelated_order_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let x = Bitvector32Term::Variable(Variable(94_001));
            let y = Bitvector32Term::Variable(Variable(94_002));
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Variable(Variable(94_100 + index as u64)),
                        Bitvector32Term::Constant(1_000),
                    ),
                    true,
                );
            }
            for term in [x.clone(), y.clone()] {
                assumptions = assumptions
                    .assume_condition(
                        ConditionTerm::signed_greater_equal(
                            term.clone(),
                            Bitvector32Term::Constant(0),
                        ),
                        true,
                    )
                    .assume_condition(
                        ConditionTerm::signed_less_equal(term, Bitvector32Term::Constant(1_000)),
                        true,
                    );
            }
            let (decision, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.decide(&ConditionTerm::signed_add_overflows(x, y))
            });
            assert_eq!(decision, Some(false));
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "fixed overflow decision is superlinear: {samples:?}"
        );
    }
}

/// `x_k = x_(k-1) + 1` executed as C: the k-th add's overflow decision must
/// not grow with the increments before it. The value once carried every
/// increment as a node, so each decision ranged a k-deep term and the chain
/// was quadratic. The decision is still made: an unbounded base is refused.
#[test]
fn increment_chain_add_work_does_not_grow_with_earlier_increments() {
    let base = Bitvector32Term::Variable(Variable(95_001));
    let bounded = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(base.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(base.clone(), Bitvector32Term::Constant(1_000_000)),
            true,
        );
    let state = CState::new();
    let increment = |value: Bitvector32Term, assumptions: &PureFactContext| {
        let expression = c_add(CExpression::Value(CValue::Int32(value)), c_int32_literal(1));
        crate::instrumentation::measure_deterministic_work(|| {
            evaluate_c_expression_paths(
                &state,
                &expression,
                assumptions,
                &mut ExecutionBudget::default(),
            )
            .expect("an increment should evaluate")
        })
    };
    let mut value = base.clone();
    let mut samples = Vec::new();
    for length in 1..=256 {
        let (paths, work) = increment(value, &bounded);
        let [path] = paths.as_slice() else {
            panic!("increment {length} of a bounded base should not split: {paths:?}");
        };
        let CExpressionOutcome::Value(CValue::Int32(next)) = &path.outcome else {
            panic!(
                "increment {length} should produce an int32: {:?}",
                path.outcome
            );
        };
        value = next.clone();
        if [16, 64, 256].contains(&length) {
            samples.push((length, work));
        }
    }
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(2)),
        "an increment's add work grows with the chain before it: {samples:?}"
    );
    let (paths, _) = increment(value, &PureFactContext::new());
    assert!(
        paths.iter().any(|path| matches!(
            path.outcome,
            CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow)
        )),
        "an unbounded base must still owe the overflow"
    );
}

/// The issue-named quantified-match curve: one query answered by
/// instantiating one guarded quantified fact, while unrelated quantified
/// facts about other memory blocks grow.
#[test]
fn quantified_fact_query_scales_near_linearly_with_unrelated_quantified_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let memory = CMemory::new();
            let data = Pointer {
                block: "quantified-data".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let fact_index = Variable(94_500);
            let target_index = Variable(94_501);
            let length = Bitvector32Term::Variable(Variable(94_502));
            let guarded_fact = forall_int32(
                fact_index,
                Proposition::Implies(
                    Box::new(Proposition::And(
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::signed_less_equal(
                                Bitvector32Term::Constant(0),
                                Bitvector32Term::Variable(fact_index),
                            ),
                            true,
                        )),
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::signed_less_than(
                                Bitvector32Term::Variable(fact_index),
                                length.clone(),
                            ),
                            true,
                        )),
                    )),
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::equal(
                            Bitvector32Term::MemoryLoad(
                                crate::kernel::intern_c_memory_ref(&memory),
                                Box::new(data.offset_by_int32_elements(Bitvector32Term::Variable(
                                    fact_index,
                                ))),
                                crate::kernel::LoadKind::Bits32,
                            ),
                            Bitvector32Term::Constant(7),
                        ),
                        true,
                    )),
                ),
            );
            let mut assumptions = PureFactContext::new().assume_proposition(guarded_fact);
            for index in 0..size {
                let unrelated_index = Variable(95_000 + index as u64 * 2);
                let unrelated = Pointer {
                    block: format!("quantified-unrelated-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                assumptions = assumptions.assume_proposition(forall_int32(
                    unrelated_index,
                    Proposition::Implies(
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::signed_less_equal(
                                Bitvector32Term::Constant(0),
                                Bitvector32Term::Variable(unrelated_index),
                            ),
                            true,
                        )),
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::equal(
                                Bitvector32Term::MemoryLoad(
                                    crate::kernel::intern_c_memory_ref(&memory),
                                    Box::new(unrelated.offset_by_int32_elements(
                                        Bitvector32Term::Variable(unrelated_index),
                                    )),
                                    crate::kernel::LoadKind::Bits32,
                                ),
                                Bitvector32Term::Constant(9),
                            ),
                            true,
                        )),
                    ),
                ));
            }
            assumptions = assumptions
                .assume_condition(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Variable(target_index),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(target_index),
                        length,
                    ),
                    true,
                );
            let target = Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: data.offset_by_int32_elements(Bitvector32Term::Variable(target_index)),
                bytes: Bitvector32Term::Constant(4),
                wide: false,
            };
            let (proved, work) =
                crate::instrumentation::measure_deterministic_work(|| assumptions.proves(&target));
            assert!(!proved, "quantified value facts grant no loadability");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "quantified fact query is superlinear: {samples:?}"
        );
    }
}

/// The issue-named long-order-path curve: deciding `first < last` across a
/// chain of strict order facts must cost work proportional to the returned
/// path, not path length times ambient fact count.
#[test]
fn long_order_path_decision_scales_near_linearly_with_path_length() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(96_000 + index as u64)),
                        Bitvector32Term::Variable(Variable(96_001 + index as u64)),
                    ),
                    true,
                );
            }
            let (decision, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.decide(&ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(96_000)),
                    Bitvector32Term::Variable(Variable(96_000 + size as u64)),
                ))
            });
            assert_eq!(decision, Some(true), "the chain proves its endpoints");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "long order path decision is superlinear: {samples:?}"
        );
    }
}

/// The dominant real shape of the order-conflict residue: loads compared
/// against constants. An owned-vector profile showed 13,343 of 20,777 deep
/// comparisons were Load~Const with zero successes. A consistent context of
/// unrelated load-versus-constant order facts must not pay a comparison per
/// pair of facts.
#[test]
fn theory_capable_order_endpoints_scale_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                let cell = Pointer {
                    block: format!("arg-memory-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                let load = Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(CMemory::new()),
                    Box::new(cell),
                    crate::kernel::LoadKind::Bits32,
                );
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_than(load, Bitvector32Term::Constant(index as u32)),
                    true,
                );
            }
            let (inconsistent, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.is_inconsistent()
            });
            assert!(!inconsistent, "unrelated load-bound facts are consistent");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "theory-capable order scanning is superlinear: {samples:?}"
        );
    }
}

/// Pins the load-resolution reach of the order-conflict fallback: a load whose
/// memory determines its value contradicts a strict order against that value.
/// The comparison enters through `memory_loads_proven_equal`'s resolution step,
/// not through any equality fact.
#[test]
fn derived_order_contradiction_resolves_load_endpoints() {
    let cell = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().store(cell.clone(), int32(Bitvector32Term::Constant(7)));
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(cell),
        crate::kernel::LoadKind::Bits32,
    );
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(load, Bitvector32Term::Constant(7)),
        true,
    );

    assert!(
        assumptions.is_inconsistent(),
        "a load that resolves to 7 cannot be strictly below 7"
    );
}

/// Pins the cross-snapshot reach of the order-conflict fallback: loads of one
/// untouched cell from two snapshots related by a recorded effect are equal,
/// so a strict order between them is a contradiction. Neither form is an
/// equality-graph edge.
#[test]
fn derived_order_contradiction_bridges_snapshot_loads() {
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    // The untouched cell is the `int32` at offset zero; a width-less load
    // there spans eight bytes and the store at offset four does touch it.
    crate::kernel::eval::declare_load_access_width(&preserved, 4);
    let before = CMemory::new();
    let after = before
        .clone()
        .store(written.clone(), int32(Bitvector32Term::Constant(1)));
    let before_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(preserved.clone()),
        crate::kernel::LoadKind::Bits32,
    );
    let after_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(after.clone()),
        Box::new(preserved),
        crate::kernel::LoadKind::Bits32,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before,
            after,
            writes: vec![(written, 4)],
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

/// Pins the addend-level equality-graph reach of the fallback: `x + 1` and
/// `y + 1` are related only through the fact `x == y` consumed inside the add
/// rule's addend comparison — the whole sums never appear in any equality fact.
#[test]
fn derived_order_contradiction_uses_graph_equal_addends() {
    let x = Bitvector32Term::Variable(Variable(97_010));
    let y = Bitvector32Term::Variable(Variable(97_011));
    let middle = Bitvector32Term::Variable(Variable(97_012));
    let left_sum = Bitvector32Term::add(x.clone(), Bitvector32Term::Constant(1));
    let right_sum = Bitvector32Term::add(y.clone(), Bitvector32Term::Constant(1));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(x, y), true)
        .assume_condition(
            ConditionTerm::signed_less_than(left_sum, middle.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(middle, right_sum), true);

    assert!(
        assumptions.is_inconsistent(),
        "`x + 1 < middle` and `middle < y + 1` contradict through `x == y`"
    );
}

#[test]
fn repeated_context_inconsistency_queries_do_not_rescan_facts() {
    let x = Bitvector32Term::Variable(Variable(93_201));
    let y = Bitvector32Term::Variable(Variable(93_202));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(x.clone(), y.clone()), true)
        .assume_condition(ConditionTerm::signed_less_than(y, x), true);
    let _scope = assumptions.enter_id_scope();
    PureFactContext::reset_context_inconsistency_full_scans();
    assert!(assumptions.is_inconsistent());
    assert_eq!(PureFactContext::context_inconsistency_full_scans(), 1);
    assert!(assumptions.is_inconsistent());
    assert_eq!(PureFactContext::context_inconsistency_full_scans(), 1);
}

/// Signed intervals are reconstructed over the term's structure with no
/// depth cut: a sum of any depth over a bounded variable ranges.
#[test]
fn signed_intervals_range_sums_of_any_depth() {
    let x = Bitvector32Term::Variable(Variable(7_200_000));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(x.clone(), Bitvector32Term::Constant(1)),
            true,
        );
    for depth in [8, 32, 64, 128] {
        let mut sum = x.clone();
        for _ in 0..depth {
            sum = Bitvector32Term::Add(Box::new(sum), Box::new(x.clone()));
        }
        assert_eq!(
            assumptions.decide_from_overflow_facts(&ConditionTerm::Bitvector32SignedAddOverflows(
                Box::new(sum),
                Box::new(x.clone()),
            )),
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
        let variable = |index: u64| Bitvector32Term::Variable(Variable(7_300_000 + index));
        let mut assumptions = PureFactContext::new();
        for index in 0..length {
            let next = if index + 1 == length {
                Bitvector32Term::Constant(length as u32)
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

/// A simp derivation has no step budget: a balanced conjunction of any
/// width whose parts are exact facts derives, its work following the goal.
#[test]
fn simp_derivations_have_no_step_budget() {
    for width in [64u64, 128, 256, 512] {
        let variable = |index: u64| Bitvector32Term::Variable(Variable(7_500_000 + index));
        let condition = |index: u64| {
            ConditionTerm::equal(variable(index), Bitvector32Term::Constant(index as u32))
        };
        let mut assumptions = PureFactContext::new();
        for index in 0..width {
            assumptions = assumptions.assume_condition(condition(index), true);
        }
        let mut parts = (0..width)
            .map(|index| Proposition::ConditionIs(condition(index), true))
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
            assumptions.derive_simp_proposition(&parts[0]).is_some(),
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
        let i_bits = Bitvector32Term::Variable(i);
        let antecedent = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(
                    i_bits.clone(),
                    Bitvector32Term::Constant(width as u32),
                ),
                true,
            )),
        );
        // A balanced disjunction: its depth is logarithmic in the width, so
        // the width is what the proof exercises.
        let mut cases = (0..width)
            .map(|value| {
                Proposition::ConditionIs(
                    ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(value as u32)),
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
            PureFactContext::new().proves(&goal),
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
        let x = Bitvector32Term::Variable(Variable(7_700_000 + u64::from(width)));
        let case = |value: u32| {
            Proposition::ConditionIs(
                ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(value)),
                true,
            )
        };
        let disjunction = (0..width - 1).rev().fold(case(width - 1), |rest, value| {
            Proposition::Or(Box::new(case(value)), Box::new(rest))
        });
        let assumptions = PureFactContext::new().assume_proposition(disjunction);
        let nonnegative = Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), x.clone()),
            true,
        );
        assert!(!assumptions.proves(&nonnegative));
        assert_checkable_derivation(&assumptions, &nonnegative);
    }
}

#[test]
fn integer_machine_operation_axioms_agree_with_boundary_models() {
    // Evaluate the emitted theorem independently, including modular machine
    // arithmetic and the signed overflow guard. In particular, the guard must
    // exclude the concrete assignments that falsify an unguarded equality.
    fn bits(term: &Bitvector32Term, a: i32, b: i32) -> u32 {
        match term {
            Bitvector32Term::Variable(variable) if *variable == Variable(910) => a as u32,
            Bitvector32Term::Variable(variable) if *variable == Variable(911) => b as u32,
            Bitvector32Term::Constant(value) => *value,
            Bitvector32Term::Add(left, right) => bits(left, a, b).wrapping_add(bits(right, a, b)),
            Bitvector32Term::Subtract(left, right) => {
                bits(left, a, b).wrapping_sub(bits(right, a, b))
            }
            _ => panic!("unexpected machine term: {term:?}"),
        }
    }
    fn integer(term: &IntegerTerm, a: i32, b: i32) -> num_bigint::BigInt {
        match term {
            IntegerTerm::Constant(value) => value.clone(),
            IntegerTerm::Machine(value) => {
                assert_eq!(value.ty(), MachineIntegerType::Int32);
                (bits(value.value(), a, b) as i32).into()
            }
            IntegerTerm::Add(left, right) => integer(left, a, b) + integer(right, a, b),
            IntegerTerm::Subtract(left, right) => integer(left, a, b) - integer(right, a, b),
            _ => panic!("unexpected Integer term: {term:?}"),
        }
    }

    for (safety, subtract) in [
        (
            prove_int32_add_defined_by_integer_bounds(
                Bitvector32Term::Variable(Variable(910)),
                Bitvector32Term::Variable(Variable(911)),
            ),
            false,
        ),
        (
            prove_int32_subtract_defined_by_integer_bounds(
                Bitvector32Term::Variable(Variable(910)),
                Bitvector32Term::Variable(Variable(911)),
            ),
            true,
        ),
    ] {
        let Proposition::Implies(lower, tail) = safety.proposition() else {
            panic!("missing lower bound")
        };
        let Proposition::Implies(upper, result) = tail.as_ref() else {
            panic!("missing upper bound")
        };
        let Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(exact_lower, min), true) =
            lower.as_ref()
        else {
            panic!("wrong lower bound")
        };
        let Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(exact_upper, max), true) =
            upper.as_ref()
        else {
            panic!("wrong upper bound")
        };
        let (x, y) = match (result.as_ref(), subtract) {
            (
                Proposition::ConditionIs(ConditionTerm::Bitvector32SignedAddOverflows(x, y), false),
                false,
            )
            | (
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedSubtractOverflows(x, y),
                    false,
                ),
                true,
            ) => (x, y),
            _ => panic!("wrong safety conclusion"),
        };
        for a in [i32::MIN, -1, 0, 1, i32::MAX] {
            for b in [i32::MIN, -1, 0, 1, i32::MAX] {
                let in_range = integer(exact_lower, a, b) >= integer(min, a, b)
                    && integer(exact_upper, a, b) <= integer(max, a, b);
                let (x, y) = (
                    i64::from(bits(x, a, b) as i32),
                    i64::from(bits(y, a, b) as i32),
                );
                let exact = if subtract { x - y } else { x + y };
                assert_eq!(in_range, i32::try_from(exact).is_ok(), "{a}, {b}");
            }
        }
    }
    for theorem in [
        prove_int32_add_to_integer(
            Bitvector32Term::Variable(Variable(910)),
            Bitvector32Term::Variable(Variable(911)),
        ),
        prove_int32_subtract_to_integer(
            Bitvector32Term::Variable(Variable(910)),
            Bitvector32Term::Variable(Variable(911)),
        ),
    ] {
        let Proposition::Implies(guard, conclusion) = theorem.proposition() else {
            panic!("missing definedness guard")
        };
        let Proposition::ConditionIs(guard, false) = guard.as_ref() else {
            panic!("wrong guard polarity")
        };
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) =
            conclusion.as_ref()
        else {
            panic!("wrong conclusion")
        };
        let mut defined = 0;
        let mut excluded = 0;
        for a in [i32::MIN, i32::MIN + 1, -1, 0, 1, i32::MAX - 1, i32::MAX] {
            for b in [i32::MIN, i32::MIN + 1, -1, 0, 1, i32::MAX - 1, i32::MAX] {
                let exact = match guard {
                    ConditionTerm::Bitvector32SignedAddOverflows(x, y) => {
                        i64::from(bits(x, a, b) as i32) + i64::from(bits(y, a, b) as i32)
                    }
                    ConditionTerm::Bitvector32SignedSubtractOverflows(x, y) => {
                        i64::from(bits(x, a, b) as i32) - i64::from(bits(y, a, b) as i32)
                    }
                    _ => panic!("wrong definedness guard"),
                };
                let equality = integer(left, a, b) == integer(right, a, b);
                if i32::try_from(exact).is_ok() {
                    defined += 1;
                    assert!(equality, "unsound bridge at {a}, {b}");
                } else {
                    excluded += 1;
                    assert!(
                        !equality,
                        "overflow counterexample should falsify the unguarded law"
                    );
                }
            }
        }
        assert!(defined > 0 && excluded > 0);
    }
}

#[test]
fn int32_order_observation_axiom_agrees_with_boundary_model() {
    fn bits(term: &Bitvector32Term, left: i32, right: i32) -> i32 {
        match term {
            Bitvector32Term::Variable(variable) if *variable == Variable(920) => left,
            Bitvector32Term::Variable(variable) if *variable == Variable(921) => right,
            Bitvector32Term::Constant(value) => *value as i32,
            _ => panic!("unexpected machine term: {term:?}"),
        }
    }

    fn integer(term: &IntegerTerm, left: i32, right: i32) -> i64 {
        match term {
            IntegerTerm::Machine(value) => {
                assert_eq!(value.ty(), MachineIntegerType::Int32);
                i64::from(bits(value.value(), left, right))
            }
            _ => panic!("unexpected Integer term: {term:?}"),
        }
    }

    let theorem = prove_int32_less_equal_to_integer(
        Bitvector32Term::Variable(Variable(920)),
        Bitvector32Term::Variable(Variable(921)),
    );
    let Proposition::Implies(guard, conclusion) = theorem.proposition() else {
        panic!("missing order premise")
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(left, right), true) =
        guard.as_ref()
    else {
        panic!("wrong C order premise")
    };
    let Proposition::ConditionIs(
        ConditionTerm::IntegerLessEqual(left_integer, right_integer),
        true,
    ) = conclusion.as_ref()
    else {
        panic!("wrong Integer order conclusion")
    };

    for left_value in [i32::MIN, i32::MIN + 1, -1, 0, 1, i32::MAX - 1, i32::MAX] {
        for right_value in [i32::MIN, i32::MIN + 1, -1, 0, 1, i32::MAX - 1, i32::MAX] {
            let c_order =
                bits(left, left_value, right_value) <= bits(right, left_value, right_value);
            let integer_order = integer(left_integer, left_value, right_value)
                <= integer(right_integer, left_value, right_value);
            assert_eq!(c_order, integer_order, "{left_value} <= {right_value}");
        }
    }
}

#[test]
fn uint32_integer_equality_bridge_matches_independent_unsigned_boundary_values() {
    let theorem = prove_uint32_equal_of_to_integer(
        Bitvector32Term::Variable(Variable(924)),
        Bitvector32Term::Variable(Variable(925)),
    );
    let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
        panic!("equality needs its Integer premise");
    };
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = premise.as_ref() else {
        panic!("expected exact Integer equality");
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(x, y), true) = conclusion.as_ref()
    else {
        panic!("expected exact machine equality");
    };
    let (IntegerTerm::Machine(a), IntegerTerm::Machine(b)) = (a.as_ref(), b.as_ref()) else {
        panic!("expected machine observations");
    };
    assert_eq!(a.ty(), MachineIntegerType::UInt32);
    assert_eq!(b.ty(), MachineIntegerType::UInt32);
    assert_eq!(a.value(), x.as_ref());
    assert_eq!(b.value(), y.as_ref());
    for left in [
        0,
        1,
        0x7fff_ffff,
        0x8000_0000,
        0x8000_0001,
        u32::MAX - 1,
        u32::MAX,
    ] {
        for right in [
            0,
            1,
            0x7fff_ffff,
            0x8000_0000,
            0x8000_0001,
            u32::MAX - 1,
            u32::MAX,
        ] {
            // The unsigned observation and the bit pattern agree, including
            // patterns above the signed sign bit.
            let observed_equal = u64::from(left) == u64::from(right);
            let bits_equal = left == right;
            assert_eq!(observed_equal, bits_equal, "{left}, {right}");
        }
    }
}

#[test]
fn int32_integer_equality_bridge_matches_independent_signed_boundary_values() {
    let theorem = prove_int32_equal_of_to_integer(
        Bitvector32Term::Variable(Variable(922)),
        Bitvector32Term::Variable(Variable(923)),
    );
    let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
        panic!("equality needs its Integer premise");
    };
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = premise.as_ref() else {
        panic!("expected exact Integer equality");
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(x, y), true) = conclusion.as_ref()
    else {
        panic!("expected exact machine equality");
    };
    let (IntegerTerm::Machine(a), IntegerTerm::Machine(b)) = (a.as_ref(), b.as_ref()) else {
        panic!("expected machine observations");
    };
    assert_eq!(a.ty(), MachineIntegerType::Int32);
    assert_eq!(b.ty(), MachineIntegerType::Int32);
    assert_eq!(a.value(), x.as_ref());
    assert_eq!(b.value(), y.as_ref());
    for left in [i32::MIN, i32::MIN + 1, -1, 0, 1, i32::MAX - 1, i32::MAX] {
        for right in [i32::MIN, i32::MIN + 1, -1, 0, 1, i32::MAX - 1, i32::MAX] {
            // Evaluate the signed observation and the bit-pattern equality
            // independently, including pairs with different signs.
            let observed_equal = i64::from(left) == i64::from(right);
            let bits_equal = left as u32 == right as u32;
            assert_eq!(observed_equal, bits_equal, "{left}, {right}");
        }
    }
}

#[test]
fn integer_machine_round_trip_axioms_hold_in_independent_boundary_models() {
    use num_bigint::BigInt;
    use num_traits::One;

    fn shape(destination: MachineIntegerType) -> (usize, bool) {
        match destination {
            MachineIntegerType::Int8 => (8, true),
            MachineIntegerType::Int16 => (16, true),
            MachineIntegerType::Int32 => (32, true),
            MachineIntegerType::UInt8 => (8, false),
            MachineIntegerType::UInt16 => (16, false),
            MachineIntegerType::UInt32 => (32, false),
            MachineIntegerType::Int64 => (64, true),
            MachineIntegerType::UInt64 => (64, false),
            MachineIntegerType::Int128 => (128, true),
            MachineIntegerType::UInt128 => (128, false),
        }
    }
    fn integer(term: &IntegerTerm, input: &BigInt) -> BigInt {
        match term {
            IntegerTerm::Constant(value) => value.clone(),
            IntegerTerm::Variable(variable) if *variable == Variable(971) => input.clone(),
            IntegerTerm::Machine(observation) => {
                let Bitvector32Term::IntegerToMachine { value, destination } = observation.value()
                else {
                    panic!("expected the emitted reverse conversion");
                };
                assert_eq!(observation.ty(), *destination);
                let (width, signed) = shape(*destination);
                let modulus = BigInt::one() << width;
                let bits = ((integer(value, input) % &modulus) + &modulus) % &modulus;
                if signed && bits >= (&modulus >> 1usize) {
                    bits - modulus
                } else {
                    bits
                }
            }
            _ => panic!("unexpected term in round-trip axiom"),
        }
    }
    fn evaluate(proposition: &Proposition, input: &BigInt) -> bool {
        match proposition {
            Proposition::Implies(premise, conclusion) => {
                !evaluate(premise, input) || evaluate(conclusion, input)
            }
            Proposition::ConditionIs(condition, expected) => {
                let result = match condition {
                    ConditionTerm::IntegerGreaterEqual(left, right) => {
                        integer(left, input) >= integer(right, input)
                    }
                    ConditionTerm::IntegerLessEqual(left, right) => {
                        integer(left, input) <= integer(right, input)
                    }
                    ConditionTerm::IntegerEqual(left, right) => {
                        integer(left, input) == integer(right, input)
                    }
                    _ => panic!("unexpected condition in round-trip axiom"),
                };
                result == *expected
            }
            _ => panic!("unexpected proposition in round-trip axiom"),
        }
    }
    for destination in [
        MachineIntegerType::Int8,
        MachineIntegerType::Int16,
        MachineIntegerType::Int32,
        MachineIntegerType::UInt8,
        MachineIntegerType::UInt16,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let (width, signed) = shape(destination);
        let span = BigInt::one() << if signed { width - 1 } else { width };
        let lower = if signed { -&span } else { BigInt::from(0) };
        let upper: BigInt = &span - 1;
        let axiom =
            prove_integer_machine_round_trip(IntegerTerm::Variable(Variable(971)), destination);
        let Proposition::Implies(_, rest) = axiom.proposition() else {
            panic!()
        };
        let Proposition::Implies(_, conclusion) = rest.as_ref() else {
            panic!()
        };
        for input in [
            &lower - 1,
            lower.clone(),
            &lower + 1,
            BigInt::from(-1),
            BigInt::from(0),
            BigInt::from(1),
            &upper - 1,
            upper.clone(),
            &upper + 1,
            -(BigInt::one() << 128usize),
            BigInt::one() << 128usize,
        ] {
            assert!(
                evaluate(axiom.proposition(), &input),
                "{destination:?}: {input}"
            );
            assert_eq!(
                evaluate(conclusion, &input),
                input >= lower && input <= upper,
                "{destination:?}: {input}"
            );
        }
    }
}

/// The discharge rule shared by `add_required_proof_obligation_with_context`
/// and the call-requirement sites in `prepare_verified_function_call`.
///
/// It decides exactly three things: an exactly available fact, one bare
/// condition the frozen checker decides, and an atomic memory or resource
/// proposition. A proposition with logical structure is never discharged
/// here, however easily a general prover would have derived it; it is
/// emitted for a Surface tactic instead.
#[test]
fn required_obligation_discharge_is_exact_and_refuses_logical_structure() {
    let value = Bitvector32Term::Variable(Variable(97_100));
    let positive = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let other = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            Bitvector32Term::Variable(Variable(97_101)),
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

    // A disjunction with an exactly available arm, a conjunction with an
    // unavailable conjunct, and an implication with a refuted antecedent are
    // all derivable by the general prover and none of them is discharged.
    let disjunction = Proposition::Or(Box::new(positive.clone()), Box::new(other.clone()));
    assert!(!required_obligation_is_exactly_discharged(
        &assumptions,
        &disjunction
    ));
    let implication = Proposition::Implies(Box::new(other.clone()), Box::new(nonnegative.clone()));
    assert!(!required_obligation_is_exactly_discharged(
        &assumptions,
        &implication
    ));
    assert!(
        assumptions.proves(&disjunction),
        "the general prover must still be the thing this route deliberately refuses"
    );
    assert!(assumptions.proves(&implication));

    // And the emitted obligation is the required (non-assumable) kind,
    // carrying its context.
    let mut obligations = Vec::new();
    add_required_proof_obligation_with_context(
        &mut obligations,
        &assumptions,
        disjunction.clone(),
        Some("callee precondition"),
        None,
    );
    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].proposition(), &disjunction);
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
    let start = Bitvector32Term::Variable(Variable(150));
    let end = Bitvector32Term::Variable(Variable(151));

    let left = Bitvector32Term::range_fold(
        start.clone(),
        end.clone(),
        Bitvector32Term::Constant(0),
        shared,
        item,
        Bitvector32Term::Variable(shared),
    );
    let right = Bitvector32Term::range_fold(
        start,
        end,
        Bitvector32Term::Constant(0),
        right_accumulator,
        item,
        Bitvector32Term::Variable(shared),
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
    let start = Bitvector32Term::Variable(Variable(164));
    let end = Bitvector32Term::Variable(Variable(165));

    let nest = |inner_accumulator, inner_body| {
        Bitvector32Term::range_fold(
            start.clone(),
            end.clone(),
            Bitvector32Term::Constant(0),
            outer_accumulator,
            outer_item,
            Bitvector32Term::add(
                Bitvector32Term::range_fold(
                    start.clone(),
                    end.clone(),
                    Bitvector32Term::Constant(0),
                    inner_accumulator,
                    inner_item,
                    inner_body,
                ),
                Bitvector32Term::Constant(1),
            ),
        )
    };

    // The inner fold rebinds `outer_accumulator`, so its body reads its own
    // accumulator and it returns its initial value.
    let shadowing = nest(
        outer_accumulator,
        Bitvector32Term::Variable(outer_accumulator),
    );
    // The inner fold binds a different name, so the same body reads the
    // enclosing accumulator.
    let reading = nest(
        inner_accumulator,
        Bitvector32Term::Variable(outer_accumulator),
    );

    let assumptions = PureFactContext::new();
    assert!(!assumptions.range_fold_terms_alpha_equivalent(&shadowing, &reading));
    assert!(!assumptions.bitvector_terms_proven_equal(&shadowing, &reading));

    // Renaming every binder of either one keeps it equal to itself: the
    // distinction above is about binding, not about spelling.
    let renamed_shadowing = Bitvector32Term::range_fold(
        start.clone(),
        end.clone(),
        Bitvector32Term::Constant(0),
        Variable(170),
        Variable(171),
        Bitvector32Term::add(
            Bitvector32Term::range_fold(
                start.clone(),
                end.clone(),
                Bitvector32Term::Constant(0),
                Variable(172),
                Variable(173),
                Bitvector32Term::Variable(Variable(172)),
            ),
            Bitvector32Term::Constant(1),
        ),
    );
    assert!(assumptions.range_fold_terms_alpha_equivalent(&shadowing, &renamed_shadowing));

    let renamed_reading = Bitvector32Term::range_fold(
        start,
        end,
        Bitvector32Term::Constant(0),
        Variable(180),
        Variable(181),
        Bitvector32Term::add(
            Bitvector32Term::range_fold(
                Bitvector32Term::Variable(Variable(164)),
                Bitvector32Term::Variable(Variable(165)),
                Bitvector32Term::Constant(0),
                Variable(182),
                Variable(183),
                Bitvector32Term::Variable(Variable(180)),
            ),
            Bitvector32Term::Constant(1),
        ),
    );
    assert!(assumptions.range_fold_terms_alpha_equivalent(&reading, &renamed_reading));
    assert!(!assumptions.range_fold_terms_alpha_equivalent(&shadowing, &renamed_reading));
}

#[test]
fn range_fold_alpha_identity_keeps_renamed_binders_and_shared_free_variables_equal() {
    let free = Variable(190);
    let start = Bitvector32Term::Variable(Variable(191));
    let end = Bitvector32Term::Variable(Variable(192));

    // `acc + item + free`, under two disjoint sets of binder names.
    let summed = |accumulator, item| {
        Bitvector32Term::range_fold(
            start.clone(),
            end.clone(),
            Bitvector32Term::Constant(0),
            accumulator,
            item,
            Bitvector32Term::add(
                Bitvector32Term::add(
                    Bitvector32Term::Variable(accumulator),
                    Bitvector32Term::Variable(item),
                ),
                Bitvector32Term::Variable(free),
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
        &Bitvector32Term::Variable(Variable(197)),
    );
    assert!(!assumptions.range_fold_terms_alpha_equivalent(&left, &other_free));
}

#[test]
fn range_fold_alpha_identity_equates_nested_folds_under_renamed_binders() {
    let start = Bitvector32Term::Variable(Variable(200));
    let end = Bitvector32Term::Variable(Variable(201));

    // `fold(|acc, k| acc + fold(|total, j| total + k))`: the inner body reads
    // the enclosing item binder, so the two nestings only match when that
    // outer binder is aligned as well.
    let nested = |accumulator, item, inner_accumulator, inner_item| {
        Bitvector32Term::range_fold(
            start.clone(),
            end.clone(),
            Bitvector32Term::Constant(0),
            accumulator,
            item,
            Bitvector32Term::add(
                Bitvector32Term::Variable(accumulator),
                Bitvector32Term::range_fold(
                    start.clone(),
                    end.clone(),
                    Bitvector32Term::Constant(0),
                    inner_accumulator,
                    inner_item,
                    Bitvector32Term::add(
                        Bitvector32Term::Variable(inner_accumulator),
                        Bitvector32Term::Variable(item),
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
    let inner_item_instead = Bitvector32Term::range_fold(
        start.clone(),
        end.clone(),
        Bitvector32Term::Constant(0),
        Variable(206),
        Variable(207),
        Bitvector32Term::add(
            Bitvector32Term::Variable(Variable(206)),
            Bitvector32Term::range_fold(
                start,
                end,
                Bitvector32Term::Constant(0),
                Variable(208),
                Variable(209),
                Bitvector32Term::add(
                    Bitvector32Term::Variable(Variable(208)),
                    Bitvector32Term::Variable(Variable(209)),
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
    let bounded = Bitvector32Term::Variable(Variable(97_500));
    let middle = Bitvector32Term::Variable(Variable(97_501));
    let inner = Bitvector32Term::Variable(Variable(97_502));
    let zero = Bitvector32Term::Constant(0);
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
                    ConditionTerm::signed_greater_equal(
                        inner.clone(),
                        Bitvector32Term::Constant(1),
                    ),
                    true,
                );
            for index in 0..size {
                let unrelated = Bitvector32Term::Variable(Variable(97_600 + index as u64));
                assumptions = assumptions
                    .assume_condition(
                        ConditionTerm::signed_greater_equal(unrelated.clone(), zero.clone()),
                        true,
                    )
                    .assume_condition(
                        ConditionTerm::signed_less_equal(
                            unrelated,
                            Bitvector32Term::Constant(1_000),
                        ),
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

/// The guarded-implication index selects `defined(e) implies a == b` facts
/// by the consequent's operands: a goal naming `a` finds the one guarded
/// equality about `a`, and the lookup's work does not grow with unrelated
/// guarded equalities. An implication under an ordinary condition is not
/// indexed: applying it stays an explicit `extract`.
#[test]
fn guarded_implication_lookup_is_keyed_by_consequent_operands() {
    let guarded = |index: u64| {
        let old = Bitvector32Term::Variable(Variable(98_000 + index));
        let delta = Bitvector32Term::Variable(Variable(98_500 + index));
        let new = Bitvector32Term::Variable(Variable(99_000 + index));
        Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedAddOverflows(
                    Box::new(old.clone()),
                    Box::new(delta.clone()),
                ),
                false,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(new, Bitvector32Term::Add(Box::new(old), Box::new(delta))),
                true,
            )),
        )
    };
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(99_000)),
            Bitvector32Term::Constant(1),
        ),
        true,
    );
    let bound = |value: u32| {
        Proposition::ConditionIs(
            ConditionTerm::signed_less_than(
                Bitvector32Term::Variable(Variable(97_900)),
                Bitvector32Term::Constant(value),
            ),
            true,
        )
    };
    let ordinary_guard = Proposition::Implies(Box::new(bound(10)), Box::new(goal.clone()));
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut facts = vec![guarded(0), ordinary_guard.clone()];
            facts.extend((1..size).map(guarded));
            let facts = crate::kernel::proof::ProofFacts::from_ordered(&facts);
            let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.guarded_implications_mentioning(&goal)
            });
            assert_eq!(selected, vec![guarded(0)]);
            assert!(work > 0, "the lookup charges the buckets it visits");
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(8),
            "guarded-equality lookup grew with unrelated facts: {samples:?}"
        );
    }
}

/// Substituting a quantifier's binder into a snapshot it does not occur in
/// rewrites the snapshot once; every later substitution of that variable into
/// that snapshot is a memo hit, whatever the replacement.
#[test]
fn snapshot_substitution_of_an_absent_variable_is_memoized() {
    let mut memory = CMemory::new();
    for index in 0..64 {
        memory = memory.with_block(format!("snapshot-memo-{index}"), 4);
    }
    let absent = Variable(434_000);
    let (_, first) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
            &memory,
            absent,
            &Bitvector32Term::Constant(1),
        )
    });
    let (_, second) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::reasoning::substitute_bitvector_variable_in_memory(
            &memory,
            absent,
            &Bitvector32Term::Constant(2),
        )
    });
    assert!(
        first >= 64,
        "the first substitution walks the snapshot: {first}"
    );
    assert!(second <= 2, "the repeat is a memo hit: {second}");
}

/// Constant normalization keeps its decisions when its classes are built
/// incrementally: a counter chain resolves whatever order its facts arrive
/// in, a second constant anywhere in a class makes that class ambiguous (and
/// only that class), and withdrawing or replacing the conflicting fact
/// restores the unique constant.
#[test]
fn constant_normalization_classes_detect_ambiguity_in_any_insertion_order() {
    let counter = |index: u64| Bitvector32Term::Variable(Variable(930_200 + index));
    let successor = |index: u64| {
        ConditionTerm::equal(
            counter(index + 1),
            Bitvector32Term::add(counter(index), 1u32.into()),
        )
    };
    let start = ConditionTerm::equal(counter(0), Bitvector32Term::Constant(0));
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

    let conflict = ConditionTerm::equal(counter(2), Bitvector32Term::Constant(7));
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
    let alias = Bitvector32Term::Variable(Variable(930_299));
    let joined = ambiguous
        .clone()
        .assume_condition(ConditionTerm::equal(alias.clone(), counter(4)), true);
    assert_eq!(
        joined.known_signed_constant_after_normalization(&alias),
        None
    );

    let withdrawn = ambiguous.without_exact_fact(&Proposition::ConditionIs(conflict.clone(), true));
    assert_eq!(
        withdrawn.known_signed_constant_after_normalization(&counter(4)),
        Some(4),
        "withdrawing the conflict restores the chain's constant"
    );
    let replaced = ambiguous.clone().assume_condition(conflict, false);
    assert_eq!(
        replaced.known_signed_constant_after_normalization(&counter(4)),
        Some(4),
        "replacing the conflict by its negation restores the chain's constant"
    );
}

#[test]
fn reflexive_comparisons_decide_without_facts_and_strict_ones_are_false() {
    let n = Bitvector32Term::Variable(Variable(89_200));
    let m = Bitvector32Term::Variable(Variable(89_201));
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
            &Proposition::ConditionIs(condition.clone(), value)
        ));
        assert!(!crate::kernel::proposition_holds_without_facts(
            &Proposition::ConditionIs(condition, !value)
        ));
    }
    // Distinct operands are not reflexive: nothing is decided without facts.
    let distinct = ConditionTerm::signed_less_equal(n, m);
    assert_eq!(distinct.reflexive_value(), None);
    assert_eq!(empty.decide(&distinct), None);
    assert!(!crate::kernel::proposition_holds_without_facts(
        &Proposition::ConditionIs(distinct, true)
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
    let x = Bitvector32Term::Variable(Variable(89_300));
    let y = Bitvector32Term::Variable(Variable(89_301));
    let plus = |t: &Bitvector32Term, c: u32| {
        Bitvector32Term::Add(Box::new(t.clone()), Box::new(Bitvector32Term::Constant(c)))
    };
    let constant = |value: i32| Bitvector32Term::Constant(value as u32);
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

/// The memory-resolution order walk reads, at each node, only the edges and
/// equalities its fact set files under that node (`OrderWalkIndex`). Its
/// answers must be the ones the full scan gives. Each row reaches its target
/// through one route the filing has to account for: the recorded-equality
/// class, exact constants on either side, a written constant node and its
/// `<=` connection to a larger constant, an offset equality at element width
/// (which the equality graph files) and at byte width (which it does not, so
/// the walk declines to file that node), a lower endpoint that is a
/// load-space variable (never filed), and the misses beside each. Every row
/// is asked filed and by full scan, as a strict and a non-strict order.
#[test]
fn memory_resolution_order_walk_agrees_with_the_full_scan() {
    let variable = |id: u64| Bitvector32Term::Variable(Variable(89_400 + id));
    let (x, y, z, w) = (variable(0), variable(1), variable(2), variable(3));
    let load_space = Bitvector32Term::Variable(Variable((1 << 40) + 89_400));
    let constant = |value: i32| Bitvector32Term::Constant(value as u32);
    let lt = ConditionTerm::signed_less_than;
    let le = ConditionTerm::signed_less_equal;
    let eq = ConditionTerm::equal;
    let offsets = |left: PointerOffsetTerm, right: PointerOffsetTerm| {
        ConditionTerm::pointer_offset_equal(left, right)
    };
    let scaled =
        |term: &Bitvector32Term, width: i64| PointerOffsetTerm::scale_int32(term.clone(), width);
    let facts = |conditions: Vec<ConditionTerm>| {
        conditions
            .into_iter()
            .fold(PureFactContext::new(), |facts, condition| {
                facts.assume_condition(condition, true)
            })
    };
    let unrelated_bounds = |mut conditions: Vec<ConditionTerm>| {
        for index in 0..16 {
            let bounded = variable(100 + index);
            conditions.push(le(constant(0), bounded.clone()));
            conditions.push(lt(bounded, w.clone()));
        }
        conditions
    };
    let cases: Vec<(
        &str,
        PureFactContext,
        Bitvector32Term,
        Bitvector32Term,
        bool,
    )> = vec![
        (
            "two edges",
            facts(vec![lt(x.clone(), y.clone()), lt(y.clone(), z.clone())]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "two edges backwards",
            facts(vec![lt(x.clone(), y.clone()), lt(y.clone(), z.clone())]),
            z.clone(),
            x.clone(),
            false,
        ),
        (
            "equality class",
            facts(vec![eq(x.clone(), y.clone()), lt(y.clone(), z.clone())]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "equality class, reversed side",
            facts(vec![eq(y.clone(), x.clone()), lt(y.clone(), z.clone())]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "equality class miss",
            facts(vec![eq(x.clone(), y.clone()), lt(z.clone(), y.clone())]),
            x.clone(),
            z.clone(),
            false,
        ),
        (
            "shared exact constant",
            facts(vec![
                eq(x.clone(), constant(5)),
                eq(y.clone(), constant(5)),
                lt(y.clone(), z.clone()),
            ]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "different exact constants",
            facts(vec![
                eq(x.clone(), constant(5)),
                eq(y.clone(), constant(6)),
                lt(y.clone(), z.clone()),
            ]),
            x.clone(),
            z.clone(),
            false,
        ),
        (
            "through a written constant node",
            facts(vec![eq(x.clone(), constant(2)), le(constant(3), z.clone())]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "constant below a constant bound",
            facts(vec![le(constant(1), z.clone())]),
            constant(0),
            z.clone(),
            true,
        ),
        (
            "constant above a constant bound",
            facts(vec![le(constant(5), z.clone())]),
            constant(7),
            z.clone(),
            false,
        ),
        (
            "constant equal to an exact endpoint",
            facts(vec![eq(y.clone(), constant(7)), lt(y.clone(), z.clone())]),
            constant(7),
            z.clone(),
            true,
        ),
        (
            "element-width offset equality",
            facts(vec![
                offsets(scaled(&x, 4), scaled(&y, 4)),
                lt(y.clone(), z.clone()),
            ]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "byte-width offset equality",
            facts(vec![
                offsets(scaled(&x, 1), scaled(&y, 1)),
                lt(y.clone(), z.clone()),
            ]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "byte-width offset equality, other side",
            facts(vec![
                offsets(scaled(&y, 1), scaled(&x, 1)),
                lt(y.clone(), z.clone()),
            ]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "constant offset equality",
            facts(vec![
                offsets(PointerOffsetTerm::Constant(8), scaled(&y, 4)),
                lt(y.clone(), z.clone()),
            ]),
            constant(2),
            z.clone(),
            true,
        ),
        (
            "load-space lower endpoint",
            facts(vec![
                eq(x.clone(), load_space.clone()),
                lt(load_space.clone(), z.clone()),
            ]),
            x.clone(),
            z.clone(),
            true,
        ),
        (
            "non-strict edge",
            facts(vec![le(x.clone(), y.clone())]),
            x.clone(),
            y.clone(),
            false,
        ),
        (
            "bounded indices beside unrelated bounds",
            facts(unrelated_bounds(vec![
                lt(x.clone(), y.clone()),
                le(constant(0), x.clone()),
                lt(y.clone(), w.clone()),
            ])),
            x.clone(),
            y.clone(),
            true,
        ),
        (
            "unordered indices beside unrelated bounds",
            facts(unrelated_bounds(vec![
                le(constant(0), x.clone()),
                lt(x.clone(), w.clone()),
                le(constant(0), y.clone()),
                lt(y.clone(), w.clone()),
            ])),
            x.clone(),
            y.clone(),
            false,
        ),
        (
            "reaching the shared bound",
            facts(unrelated_bounds(vec![
                le(constant(0), x.clone()),
                lt(x.clone(), w.clone()),
            ])),
            x.clone(),
            w.clone(),
            true,
        ),
    ];
    for (name, facts, left, right, strict_follows) in cases {
        for (order, strict) in [
            (lt(left.clone(), right.clone()), true),
            (le(left.clone(), right.clone()), false),
        ] {
            let filed = facts.proves_order_condition_for_memory_resolution(&order, true);
            let scanned = crate::kernel::assumptions::with_order_walk_full_scan(|| {
                facts.proves_order_condition_for_memory_resolution(&order, true)
            });
            assert_eq!(
                filed, scanned,
                "filed and scanned walks disagree on `{name}` ({order:?})"
            );
            if strict {
                assert_eq!(filed, strict_follows, "strict order on `{name}`");
            }
            let path = facts.has_order_path_for_memory_resolution(&left, &right, strict);
            let scanned_path = crate::kernel::assumptions::with_order_walk_full_scan(|| {
                facts.has_order_path_for_memory_resolution(&left, &right, strict)
            });
            assert_eq!(
                path, scanned_path,
                "filed and scanned paths disagree on `{name}` (strict {strict})"
            );
        }
    }
}

/// [`memory_resolution_order_walk_agrees_with_the_full_scan`] over generated
/// fact sets: a small pool of variables (one in the load-variable space),
/// constants, sums, and every fact shape the filing treats differently —
/// strict and non-strict orders, equalities, and offset equalities at both
/// widths — asked every pair of pool terms, filed and by full scan.
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn memory_resolution_order_walk_agrees_with_the_full_scan_on_generated_facts() {
    let mut pool = (0..5)
        .map(|id| Bitvector32Term::Variable(Variable(89_500 + id)))
        .collect::<Vec<_>>();
    pool.push(Bitvector32Term::Variable(Variable((1 << 40) + 89_500)));
    pool.extend([0, 1, 3, -1].map(|value: i32| Bitvector32Term::Constant(value as u32)));
    pool.push(Bitvector32Term::Add(
        Box::new(pool[0].clone()),
        Box::new(Bitvector32Term::Constant(1)),
    ));
    // Sign-bit flips, the operands of an unsigned order, which the filing
    // keys as it keys the variables they flip.
    for id in [0, 1] {
        pool.push(Bitvector32Term::bitwise_xor(
            pool[id].clone(),
            Bitvector32Term::Constant(0x8000_0000),
        ));
    }
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut next = |bound: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % bound as u64) as usize
    };
    let mut compared = 0;
    for _ in 0..120 {
        let mut facts = PureFactContext::new();
        for _ in 0..(2 + next(6)) {
            let left = pool[next(pool.len())].clone();
            let right = pool[next(pool.len())].clone();
            let condition = match next(6) {
                0 | 1 => ConditionTerm::signed_less_than(left, right),
                2 => ConditionTerm::signed_less_equal(left, right),
                3 => ConditionTerm::equal(left, right),
                width => ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(left, if width == 4 { 4 } else { 1 }),
                    PointerOffsetTerm::scale_int32(right, if width == 4 { 4 } else { 1 }),
                ),
            };
            facts = facts.assume_condition(condition, true);
        }
        for left in &pool {
            for right in &pool {
                for strict in [true, false] {
                    let filed = facts.has_order_path_for_memory_resolution(left, right, strict);
                    let scanned = crate::kernel::assumptions::with_order_walk_full_scan(|| {
                        facts.has_order_path_for_memory_resolution(left, right, strict)
                    });
                    assert_eq!(
                        filed, scanned,
                        "filed and scanned walks disagree on {left:?} -> {right:?} (strict {strict}) under {facts:?}"
                    );
                    compared += 1;
                }
            }
        }
    }
    assert!(compared > 0);
}

/// The walk's reachability memo (`OrderReachMemo`) answers exactly what a
/// fresh full-scan walk answers, whatever the earlier questions were.
/// Generated fact sets over keyable terms only — so the memo is live — mix
/// chains, cycles, strict and non-strict orders, equalities, and offset
/// equalities; every pair is asked in one order and then in the reverse
/// order, so each question meets a memo filled by different earlier walks,
/// and each is compared with the full scan, which never reads the memo.
#[test]
#[ignore = "nightly: 9s in the parallel gate"]
fn memory_resolution_order_walk_memo_agrees_with_the_full_scan() {
    let mut pool = (0..8)
        .map(|id| Bitvector32Term::Variable(Variable(89_600 + id)))
        .collect::<Vec<_>>();
    pool.extend([0, 2, -3].map(|value: i32| Bitvector32Term::Constant(value as u32)));
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = |bound: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % bound as u64) as usize
    };
    let mut compared = 0;
    let mut proved = 0;
    for _ in 0..90 {
        let mut facts = PureFactContext::new();
        // A chain through a random order of the variables, then noise.
        let mut chain = (0..8).collect::<Vec<_>>();
        for index in (1..chain.len()).rev() {
            chain.swap(index, next(index + 1));
        }
        for pair in chain.windows(2).take(2 + next(6)) {
            let (low, high) = (pool[pair[0]].clone(), pool[pair[1]].clone());
            facts = facts.assume_condition(
                if next(3) == 0 {
                    ConditionTerm::signed_less_equal(low, high)
                } else {
                    ConditionTerm::signed_less_than(low, high)
                },
                true,
            );
        }
        for _ in 0..next(5) {
            let left = pool[next(pool.len())].clone();
            let right = pool[next(pool.len())].clone();
            let condition = match next(5) {
                0 | 1 => ConditionTerm::signed_less_than(left, right),
                2 => ConditionTerm::signed_less_equal(left, right),
                3 => ConditionTerm::equal(left, right),
                _ => ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(left, 4),
                    PointerOffsetTerm::scale_int32(right, 4),
                ),
            };
            facts = facts.assume_condition(condition, true);
        }
        let questions = pool
            .iter()
            .flat_map(|left| pool.iter().map(move |right| (left, right)))
            .flat_map(|(left, right)| [true, false].map(|strict| (left, right, strict)))
            .collect::<Vec<_>>();
        for (left, right, strict) in questions.iter().chain(questions.iter().rev()) {
            let memoized = facts.has_order_path_for_memory_resolution(left, right, *strict);
            let scanned = crate::kernel::assumptions::with_order_walk_full_scan(|| {
                facts.has_order_path_for_memory_resolution(left, right, *strict)
            });
            assert_eq!(
                memoized, scanned,
                "the memoized walk and the full scan disagree on {left:?} -> {right:?} (strict {strict}) under {facts:?}"
            );
            compared += 1;
            proved += usize::from(memoized);
        }
    }
    assert!(
        proved > compared / 10 && proved < compared * 9 / 10,
        "the generated questions should mix answers: {proved} of {compared} proved"
    );
}

#[test]
fn uint64_arithmetic_constant_queries_ignore_unrelated_context() {
    let x = Bitvector32Term::Variable(Variable(990_000));
    let y = Bitvector32Term::Variable(Variable(990_001));
    let low_word_only = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(x.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    ));
    assert_eq!(
        crate::kernel::assumptions::exact_sixty_four_bit_constant(&x, true, &low_word_only),
        None
    );
    let mut prior = None;
    for size in [4, 16, 64] {
        let mut facts = PureFactContext::new()
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::uint64_equal(x.clone(), Bitvector32Term::UInt64Constant(u64::MAX)),
                true,
            ))
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::uint64_equal(y.clone(), Bitvector32Term::UInt64Constant(2)),
                true,
            ));
        for index in 0..size {
            facts = facts.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(991_000 + index)),
                    Bitvector32Term::UInt64Constant(index),
                ),
                true,
            ));
        }
        let cases = [
            (
                Bitvector32Term::uint64_divide(x.clone(), y.clone()),
                Some(u64::MAX / 2),
            ),
            (
                Bitvector32Term::uint64_remainder(x.clone(), y.clone()),
                Some(1),
            ),
            (
                Bitvector32Term::uint64_bitwise_and(x.clone(), y.clone()),
                Some(2),
            ),
            (
                Bitvector32Term::uint64_bitwise_or(x.clone(), y.clone()),
                Some(u64::MAX),
            ),
            (
                Bitvector32Term::uint64_bitwise_xor(x.clone(), y.clone()),
                Some(u64::MAX - 2),
            ),
            (Bitvector32Term::uint64_bitwise_not(x.clone()), Some(0)),
            (
                Bitvector32Term::uint64_shift_left(x.clone(), Bitvector32Term::Constant(63)),
                Some(1 << 63),
            ),
            (
                Bitvector32Term::uint64_logical_shift_right(
                    x.clone(),
                    Bitvector32Term::Constant(63),
                ),
                Some(1),
            ),
            (
                Bitvector32Term::uint64_divide(x.clone(), Bitvector32Term::UInt64Constant(0)),
                None,
            ),
            (
                Bitvector32Term::uint64_remainder(x.clone(), Bitvector32Term::UInt64Constant(0)),
                None,
            ),
            (
                Bitvector32Term::uint64_logical_shift_right(
                    x.clone(),
                    Bitvector32Term::Constant(64),
                ),
                None,
            ),
        ];
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (term, expected) in cases {
                assert_eq!(facts.wide_constant_from_equalities(&term), expected);
                assert_eq!(
                    crate::kernel::assumptions::exact_sixty_four_bit_constant(&term, true, &facts,),
                    expected.and_then(|bits| i64::try_from(bits).ok())
                );
            }
        });
        assert!(work > 0);
        if let Some(old) = prior {
            assert_eq!(work, old);
        }
        prior = Some(work);
    }
}

#[test]
fn invalid_unsigned_constant_operations_do_not_panic() {
    for term in [
        Bitvector32Term::uint64_divide(
            Bitvector32Term::UInt64Constant(1),
            Bitvector32Term::UInt64Constant(0),
        ),
        Bitvector32Term::uint64_remainder(
            Bitvector32Term::UInt64Constant(1),
            Bitvector32Term::UInt64Constant(0),
        ),
        Bitvector32Term::uint64_logical_shift_right(
            Bitvector32Term::UInt64Constant(1),
            Bitvector32Term::Constant(64),
        ),
    ] {
        assert_eq!(term.uint64_as_const(), None);
    }
    assert_eq!(
        Bitvector32Term::unsigned_divide(
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(0)
        )
        .as_const(),
        None
    );
    assert_eq!(
        Bitvector32Term::unsigned_remainder(
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(0)
        )
        .as_const(),
        None
    );
}

#[test]
fn wide_scaled_offset_congruence_checks_full_width_and_scale() {
    let index = Bitvector32Term::Variable(Variable(992_000));
    let sum = Bitvector32Term::uint64_add(index.clone(), Bitvector32Term::UInt64Constant(1));
    let offset = PointerOffsetTerm::scale_int64(sum, 4, true);
    let zero = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::uint64_equal(index.clone(), Bitvector32Term::UInt64Constant(0)),
        true,
    ));
    let four = PointerOffsetTerm::Constant(4);
    let evidence = zero
        .pointer_offset_congruence_evidence(&offset, &four)
        .unwrap();
    assert!(evidence.checks(&offset, &four, &zero));
    assert!(!evidence.checks(&offset, &PointerOffsetTerm::Constant(0), &zero));
    assert!(!evidence.checks(&offset, &four, &PureFactContext::new()));
    let high = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::uint64_equal(index.clone(), Bitvector32Term::UInt64Constant(4294967296)),
        true,
    ));
    assert!(!evidence.checks(&offset, &four, &high));
    let low_word_only = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::equal(index, Bitvector32Term::Constant(0)),
        true,
    ));
    assert!(!evidence.checks(&offset, &four, &low_word_only));
    let overflowing = PointerOffsetTerm::Int64Scaled {
        value: Box::new(Bitvector32Term::UInt64Constant(i64::MAX as u64)),
        byte_width: 2,
        unsigned: true,
    };
    assert!(
        zero.pointer_offset_congruence_evidence(&overflowing, &PointerOffsetTerm::Constant(-2))
            .is_none()
    );
}

#[test]
fn wide_constant_arithmetic_work_scales_with_selected_expression() {
    let variable = Bitvector32Term::Variable(Variable(993_000));
    let facts = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::uint64_equal(variable.clone(), Bitvector32Term::UInt64Constant(9)),
        true,
    ));
    let mut prior = None;
    for size in [4, 16, 64] {
        let mut expression = variable.clone();
        for _ in 0..size {
            expression = Bitvector32Term::UInt64Divide(
                Box::new(expression),
                Box::new(Bitvector32Term::UInt64Constant(1)),
            );
        }
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.wide_constant_from_equalities(&expression)
        });
        assert_eq!(value, Some(9));
        if let Some(old) = prior {
            assert!(work <= old * 5, "work grew from {old} to {work}");
        }
        prior = Some(work);
    }
}

/// Each uint32 order axiom holds at every boundary value: the kernel's own
/// evaluation of its premise and conclusion over constants never finds the
/// premise true and the conclusion false. The values straddle zero, the sign
/// bit the unsigned order is encoded through, and `UINT_MAX`, where an
/// increment or a decrement wraps.
#[test]
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
            PureFactContext::decide_intrinsically(condition)
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
    let constant = Bitvector32Term::Constant;
    let mut premises_true = 0usize;
    for left in BOUNDARIES {
        assert!(
            holds(&prove_uint32_positive_predecessor_strictly_decreases(
                constant(left)
            )),
            "predecessor at {left:#x}"
        );
        for right in BOUNDARIES {
            let pair: [(&str, Theorem); 8] = [
                (
                    "increment upper bound",
                    prove_uint32_increment_upper_bound(constant(left), constant(right)),
                ),
                (
                    "increment increases",
                    prove_uint32_increment_strictly_increases(constant(left), constant(right)),
                ),
                (
                    "positive difference",
                    prove_uint32_lt_implies_positive_difference(constant(left), constant(right)),
                ),
                (
                    "gt reversed",
                    prove_uint32_gt_implies_reversed_lt(constant(left), constant(right)),
                ),
                (
                    "lt reversed",
                    prove_uint32_lt_implies_reversed_gt(constant(left), constant(right)),
                ),
                (
                    "ge reversed",
                    prove_uint32_ge_implies_reversed_le(constant(left), constant(right)),
                ),
                (
                    "le reversed",
                    prove_uint32_le_implies_reversed_ge(constant(left), constant(right)),
                ),
                (
                    "difference decreases",
                    prove_uint32_difference_decreases_after_increment(
                        constant(left),
                        constant(right),
                    ),
                ),
            ];
            for last in BOUNDARIES {
                let (first, middle) = (constant(left), constant(right));
                for theorem in [
                    prove_uint32_lt_le_transitive(first.clone(), middle.clone(), constant(last)),
                    prove_uint32_le_lt_transitive(first.clone(), middle.clone(), constant(last)),
                    prove_uint32_lt_transitive(first.clone(), middle.clone(), constant(last)),
                    prove_uint32_le_transitive(first.clone(), middle.clone(), constant(last)),
                ] {
                    assert!(
                        holds(&theorem),
                        "transitivity at {left:#x}, {right:#x}, {last:#x}"
                    );
                }
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
        assert!(
            holds(&prove_uint32_positive_predecessor_strictly_decreases(
                constant(left)
            )),
            "predecessor at {left:#x}"
        );
        for theorem in [
            prove_uint32_increment_upper_bound(constant(left), constant(right)),
            prove_uint32_increment_strictly_increases(constant(left), constant(right)),
            prove_uint32_lt_implies_positive_difference(constant(left), constant(right)),
            prove_uint32_gt_implies_reversed_lt(constant(left), constant(right)),
            prove_uint32_lt_implies_reversed_gt(constant(left), constant(right)),
            prove_uint32_ge_implies_reversed_le(constant(left), constant(right)),
            prove_uint32_le_implies_reversed_ge(constant(left), constant(right)),
            prove_uint32_difference_decreases_after_increment(constant(left), constant(right)),
            prove_uint32_lt_le_transitive(
                constant(left),
                constant(right),
                constant(right.wrapping_add(left)),
            ),
            prove_uint32_le_lt_transitive(
                constant(left),
                constant(right),
                constant(right.wrapping_add(1)),
            ),
            prove_uint32_lt_transitive(
                constant(left),
                constant(right),
                constant(right.wrapping_mul(3)),
            ),
            prove_uint32_le_transitive(constant(left), constant(right), constant(left)),
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
        PureFactContext::decide_intrinsically(condition)
            .expect("a condition over constants is decided")
    };
    assert!(!conclusion_holds(
        &prove_uint32_positive_predecessor_strictly_decreases(constant(0))
    ));
    assert!(!conclusion_holds(&prove_uint32_increment_upper_bound(
        constant(5),
        constant(5)
    )));
    assert!(!conclusion_holds(
        &prove_uint32_increment_strictly_increases(constant(u32::MAX), constant(0))
    ));
    assert!(!conclusion_holds(
        &prove_uint32_lt_implies_positive_difference(constant(7), constant(7))
    ));
    assert!(!conclusion_holds(
        &prove_uint32_difference_decreases_after_increment(constant(7), constant(7))
    ));
    assert!(!conclusion_holds(&prove_uint32_lt_le_transitive(
        constant(9),
        constant(3),
        constant(5)
    )));
}

#[test]
fn singleton_bound_through_an_exact_constant_equality_retains_its_premises() {
    let i = Bitvector32Term::Variable(Variable(9_890_001));
    let n = Bitvector32Term::Variable(Variable(9_890_002));
    let lower = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), i.clone()),
        true,
    );
    let upper =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(i.clone(), n.clone()), true);
    let pinned = Proposition::ConditionIs(
        ConditionTerm::equal(n.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let goal = Proposition::ConditionIs(ConditionTerm::equal(i, n), true);
    let facts = PureFactContext::new()
        .assume_proposition(lower.clone())
        .assume_proposition(upper.clone())
        .assume_proposition(pinned.clone());
    let proof = facts
        .derive_simp_proposition(&goal)
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
    for missing in [lower, upper, pinned] {
        let restricted = facts.without_exact_fact(&missing);
        assert!(!proof.check(&restricted));
        assert!(restricted.derive_simp_proposition(&goal).is_none());
    }
}

#[test]
fn signed_integer_order_bridges_match_independent_full_width_boundary_models() {
    use num_bigint::BigInt;
    let left = Bitvector32Term::Variable(Variable(185001));
    let right = Bitvector32Term::Variable(Variable(185002));
    for (ty, width) in [
        (MachineIntegerType::Int32, 32u32),
        (MachineIntegerType::Int64, 64),
    ] {
        for reverse in [false, true] {
            let theorem = match (width, reverse) {
                (32, false) => prove_int32_less_equal_to_integer(left.clone(), right.clone()),
                (32, true) => prove_int32_less_equal_of_to_integer(left.clone(), right.clone()),
                (64, false) => prove_int64_less_equal_to_integer(left.clone(), right.clone()),
                (64, true) => prove_int64_less_equal_of_to_integer(left.clone(), right.clone()),
                _ => unreachable!(),
            };
            let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
                panic!("missing exact guard");
            };
            let (native, integer) = if reverse {
                (conclusion, premise)
            } else {
                (premise, conclusion)
            };
            match (width, native.as_ref()) {
                (
                    32,
                    Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(a, b), true),
                )
                | (
                    64,
                    Proposition::ConditionIs(ConditionTerm::Bitvector64SignedLessEqual(a, b), true),
                ) => {
                    assert_eq!(a.as_ref(), &left);
                    assert_eq!(b.as_ref(), &right);
                }
                _ => panic!("wrong native width or order"),
            }
            let Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true) =
                integer.as_ref()
            else {
                panic!("wrong mathematical relation");
            };
            let (IntegerTerm::Machine(a), IntegerTerm::Machine(b)) = (a.as_ref(), b.as_ref())
            else {
                panic!("expected exact observers");
            };
            assert_eq!(a.ty(), ty);
            assert_eq!(b.ty(), ty);
            assert_eq!(a.value(), &left);
            assert_eq!(b.value(), &right);
        }
        let maximum = if width == 32 {
            u64::from(u32::MAX)
        } else {
            u64::MAX
        };
        let sign = 1u64 << (width - 1);
        let integer = |bits: u64| {
            if bits & sign == 0 {
                BigInt::from(bits)
            } else {
                BigInt::from(bits) - (BigInt::from(1) << width)
            }
        };
        let native = |bits: u64| {
            if width == 32 {
                i64::from(bits as u32 as i32)
            } else {
                bits as i64
            }
        };
        for a in [
            0,
            1,
            2,
            sign - 2,
            sign - 1,
            sign,
            sign + 1,
            maximum - 1,
            maximum,
        ] {
            for b in [
                0,
                1,
                2,
                sign - 2,
                sign - 1,
                sign,
                sign + 1,
                maximum - 1,
                maximum,
            ] {
                assert_eq!(integer(a) <= integer(b), native(a) <= native(b));
                assert_eq!(integer(a) == integer(b), a == b);
            }
        }
    }
    let theorem = prove_int64_equal_of_to_integer(left.clone(), right.clone());
    let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
        panic!("missing equality guard");
    };
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = premise.as_ref() else {
        panic!("wrong observation equality");
    };
    let (IntegerTerm::Machine(a), IntegerTerm::Machine(b)) = (a.as_ref(), b.as_ref()) else {
        panic!("expected observers");
    };
    assert_eq!(a.ty(), MachineIntegerType::Int64);
    assert_eq!(b.ty(), MachineIntegerType::Int64);
    let Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(a, b), true) = conclusion.as_ref()
    else {
        panic!("wrong native equality width");
    };
    assert_eq!(a.as_ref(), &left);
    assert_eq!(b.as_ref(), &right);
}

#[test]
fn int64_integer_operation_bridges_match_independent_overflow_boundary_models() {
    use num_bigint::BigInt;
    let left = Bitvector32Term::Variable(Variable(186001));
    let right = Bitvector32Term::Variable(Variable(186002));
    for subtract in [false, true] {
        let theorem = if subtract {
            prove_int64_subtract_to_integer(left.clone(), right.clone())
        } else {
            prove_int64_add_to_integer(left.clone(), right.clone())
        };
        let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
            panic!("missing native definedness premise");
        };
        let native = if subtract {
            ConditionTerm::Bitvector64SignedSubtractOverflows(
                Box::new(left.clone()),
                Box::new(right.clone()),
            )
        } else {
            ConditionTerm::Bitvector64SignedAddOverflows(
                Box::new(left.clone()),
                Box::new(right.clone()),
            )
        };
        assert_eq!(premise.as_ref(), &Proposition::ConditionIs(native, false));
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(observed, exact), true) =
            conclusion.as_ref()
        else {
            panic!("wrong observation law");
        };
        let IntegerTerm::Machine(machine) = observed.as_ref() else {
            panic!("missing typed observation");
        };
        assert_eq!(machine.ty(), MachineIntegerType::Int64);
        let operation = if subtract {
            Bitvector32Term::Int64Subtract(Box::new(left.clone()), Box::new(right.clone()))
        } else {
            Bitvector32Term::Int64Add(Box::new(left.clone()), Box::new(right.clone()))
        };
        assert_eq!(machine.value(), &operation);
        let observe = |term| IntegerTerm::from_machine(MachineIntegerType::Int64, term).unwrap();
        let mathematical = if subtract {
            IntegerTerm::Subtract(observe(left.clone()).into(), observe(right.clone()).into())
        } else {
            IntegerTerm::Add(observe(left.clone()).into(), observe(right.clone()).into())
        };
        assert_eq!(exact.as_ref(), &mathematical);
        for a in [
            i64::MIN,
            i64::MIN + 1,
            -2,
            -1,
            0,
            1,
            2,
            i64::MAX - 1,
            i64::MAX,
        ] {
            for b in [
                i64::MIN,
                i64::MIN + 1,
                -2,
                -1,
                0,
                1,
                2,
                i64::MAX - 1,
                i64::MAX,
            ] {
                let exact = if subtract {
                    BigInt::from(a) - BigInt::from(b)
                } else {
                    BigInt::from(a) + BigInt::from(b)
                };
                let fits = exact >= BigInt::from(i64::MIN) && exact <= BigInt::from(i64::MAX);
                let checked = if subtract {
                    a.checked_sub(b)
                } else {
                    a.checked_add(b)
                };
                assert_eq!(checked.is_some(), fits);
                if let Some(value) = checked {
                    assert_eq!(BigInt::from(value), exact);
                }
                let theorem = if subtract {
                    prove_int64_subtract_to_integer(
                        Bitvector32Term::Int64Constant(a),
                        Bitvector32Term::Int64Constant(b),
                    )
                } else {
                    prove_int64_add_to_integer(
                        Bitvector32Term::Int64Constant(a),
                        Bitvector32Term::Int64Constant(b),
                    )
                };
                let Proposition::Implies(guard, _) = theorem.proposition() else {
                    unreachable!()
                };
                assert_eq!(
                    guard.as_ref(),
                    &Proposition::ConditionIs(ConditionTerm::Constant(!fits), false)
                );
            }
        }
    }
}

#[test]
fn uint32_add_bridges_agree_with_boundary_models() {
    fn machine(term: &Bitvector32Term, a: u32, b: u32) -> u64 {
        match term {
            Bitvector32Term::Variable(variable) if *variable == Variable(910) => u64::from(a),
            Bitvector32Term::Variable(variable) if *variable == Variable(911) => u64::from(b),
            Bitvector32Term::Constant(value) => u64::from(*value),
            Bitvector32Term::Add(left, right) => {
                u64::from((machine(left, a, b) as u32).wrapping_add(machine(right, a, b) as u32))
            }
            Bitvector32Term::Int64FromUInt32(value) => machine(value, a, b),
            Bitvector32Term::Int64Add(left, right) => machine(left, a, b) + machine(right, a, b),
            Bitvector32Term::Int64Constant(value) => u64::try_from(*value).unwrap(),
            _ => panic!("unexpected term {term:?}"),
        }
    }
    fn integer(term: &IntegerTerm, a: u32, b: u32) -> num_bigint::BigInt {
        match term {
            IntegerTerm::Constant(value) => value.clone(),
            IntegerTerm::Machine(value) => {
                assert_eq!(value.ty(), MachineIntegerType::UInt32);
                machine(value.value(), a, b).into()
            }
            IntegerTerm::Add(left, right) => integer(left, a, b) + integer(right, a, b),
            _ => panic!("unexpected Integer term {term:?}"),
        }
    }
    for theorem in [
        prove_uint32_add_to_integer(
            Bitvector32Term::Variable(Variable(910)),
            Bitvector32Term::Variable(Variable(911)),
        ),
        prove_uint32_widened_add_guard_by_integer_bound(
            Bitvector32Term::Variable(Variable(910)),
            Bitvector32Term::Variable(Variable(911)),
        ),
    ] {
        let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
            panic!("missing bound")
        };
        let Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(sum, max), true) =
            premise.as_ref()
        else {
            panic!("wrong bound")
        };
        for a in [
            0,
            1,
            255,
            65520,
            1481280,
            0x80000000,
            4294690200,
            u32::MAX - 1,
            u32::MAX,
        ] {
            for b in [0, 1, 255, 65520, 1481280, 0x80000000, u32::MAX] {
                let safe = u64::from(a) + u64::from(b) <= u64::from(u32::MAX);
                assert_eq!(integer(sum, a, b) <= integer(max, a, b), safe);
                let holds = match conclusion.as_ref() {
                    Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) => {
                        integer(left, a, b) == integer(right, a, b)
                    }
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector64SignedLessEqual(left, right),
                        true,
                    ) => machine(left, a, b) <= machine(right, a, b),
                    _ => panic!("wrong conclusion {conclusion:?}"),
                };
                assert_eq!(holds, safe, "{a} + {b}");
            }
        }
    }
}

#[test]
fn uint32_subtract_bridge_matches_unsigned_underflow_boundary_model() {
    fn machine(term: &Bitvector32Term, a: u32, b: u32) -> u32 {
        match term {
            Bitvector32Term::Variable(v) if *v == Variable(910) => a,
            Bitvector32Term::Variable(v) if *v == Variable(911) => b,
            Bitvector32Term::Constant(value) => *value,
            Bitvector32Term::Subtract(left, right) => {
                machine(left, a, b).wrapping_sub(machine(right, a, b))
            }
            Bitvector32Term::BitwiseXor(left, right) => machine(left, a, b) ^ machine(right, a, b),
            _ => panic!("unexpected subtraction term {term:?}"),
        }
    }
    fn integer(term: &IntegerTerm, a: u32, b: u32) -> num_bigint::BigInt {
        match term {
            IntegerTerm::Machine(value) => {
                assert_eq!(value.ty(), MachineIntegerType::UInt32);
                machine(value.value(), a, b).into()
            }
            IntegerTerm::Subtract(left, right) => integer(left, a, b) - integer(right, a, b),
            _ => panic!("unexpected difference observation {term:?}"),
        }
    }
    let theorem = prove_uint32_subtract_to_integer(
        Bitvector32Term::Variable(Variable(910)),
        Bitvector32Term::Variable(Variable(911)),
    );
    let Proposition::Implies(guard, conclusion) = theorem.proposition() else {
        panic!("missing no-underflow guard");
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(left, right), true) =
        guard.as_ref()
    else {
        panic!("wrong unsigned guard");
    };
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(observed, exact), true) =
        conclusion.as_ref()
    else {
        panic!("wrong observation equality");
    };
    let samples = [
        0,
        1,
        2,
        255,
        65520,
        65521,
        0x7fff_ffff,
        0x8000_0000,
        u32::MAX - 1,
        u32::MAX,
    ];
    for a in samples {
        for b in samples {
            let safe = a.checked_sub(b).is_some();
            assert_eq!(
                (machine(left, a, b) as i32) <= (machine(right, a, b) as i32),
                safe
            );
            assert_eq!(
                integer(observed, a, b),
                num_bigint::BigInt::from(a.wrapping_sub(b))
            );
            assert_eq!(
                integer(exact, a, b),
                num_bigint::BigInt::from(a) - num_bigint::BigInt::from(b)
            );
            assert_eq!(
                integer(observed, a, b) == integer(exact, a, b),
                safe,
                "{a} - {b}"
            );
        }
    }
}

#[test]
fn int32_remainder_bridge_matches_independent_signed_boundary_models() {
    let left = Bitvector32Term::Variable(Variable(940));
    let right = Bitvector32Term::Variable(Variable(941));
    let theorem = prove_int32_remainder_to_integer(left.clone(), right.clone());
    let Proposition::Implies(native_defined, rest) = theorem.proposition() else {
        panic!("missing native definedness");
    };
    let Proposition::And(nonzero, no_overflow) = native_defined.as_ref() else {
        panic!("definedness must exclude both zero and overflow");
    };
    assert_eq!(
        nonzero.as_ref(),
        &Proposition::ConditionIs(
            ConditionTerm::equal(right.clone(), Bitvector32Term::Constant(0)),
            false
        )
    );
    assert_eq!(
        no_overflow.as_ref(),
        &Proposition::ConditionIs(
            ConditionTerm::signed_divide_overflows(left.clone(), right.clone()),
            false
        )
    );
    let Proposition::Implies(integer_nonzero, conclusion) = rest.as_ref() else {
        panic!("missing mathematical domain");
    };
    let observe = |term| IntegerTerm::from_machine(MachineIntegerType::Int32, term).unwrap();
    assert_eq!(
        integer_nonzero.as_ref(),
        &Proposition::ConditionIs(
            ConditionTerm::integer_not_equal(observe(right.clone()), IntegerTerm::constant_i64(0)),
            true
        )
    );
    assert_eq!(
        conclusion.as_ref(),
        &Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                observe(Bitvector32Term::Remainder(
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
fn uint32_mul_bridge_agrees_with_checked_unsigned_boundary_models() {
    fn machine(term: &Bitvector32Term, a: u32, b: u32) -> u32 {
        match term {
            Bitvector32Term::Variable(v) if *v == Variable(910) => a,
            Bitvector32Term::Variable(v) if *v == Variable(911) => b,
            Bitvector32Term::Constant(v) => *v,
            Bitvector32Term::Multiply(left, right) => {
                machine(left, a, b).wrapping_mul(machine(right, a, b))
            }
            Bitvector32Term::UnsignedDivide(left, right) => {
                machine(left, a, b) / machine(right, a, b)
            }
            Bitvector32Term::BitwiseXor(left, right) => machine(left, a, b) ^ machine(right, a, b),
            _ => panic!("unexpected unsigned multiplication term {term:?}"),
        }
    }
    fn integer(term: &IntegerTerm, a: u32, b: u32) -> num_bigint::BigInt {
        match term {
            IntegerTerm::Constant(value) => value.clone(),
            IntegerTerm::Machine(value) => {
                assert_eq!(value.ty(), MachineIntegerType::UInt32);
                machine(value.value(), a, b).into()
            }
            IntegerTerm::Multiply(left, right) => integer(left, a, b) * integer(right, a, b),
            _ => panic!("unexpected product observation {term:?}"),
        }
    }
    fn holds(p: &Proposition, a: u32, b: u32) -> bool {
        match p {
            // Short-circuiting is essential for the zero-factor branch.
            Proposition::Or(left, right) => holds(left, a, b) || holds(right, a, b),
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
                machine(left, a, b) == machine(right, a, b)
            }
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(left, right),
                true,
            ) => (machine(left, a, b) as i32) <= (machine(right, a, b) as i32),
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) => {
                integer(left, a, b) == integer(right, a, b)
            }
            Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(left, right), true) => {
                integer(left, a, b) <= integer(right, a, b)
            }
            _ => panic!("unexpected multiplication bridge proposition {p:?}"),
        }
    }
    let theorem = prove_uint32_mul_to_integer(
        Bitvector32Term::Variable(Variable(910)),
        Bitvector32Term::Variable(Variable(911)),
    );
    let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
        panic!("missing no-wrap guard")
    };
    let guard_theorem = prove_uint32_mul_guard_by_integer_bound(
        Bitvector32Term::Variable(Variable(910)),
        Bitvector32Term::Variable(Variable(911)),
    );
    let Proposition::Implies(product_bound, native_guard) = guard_theorem.proposition() else {
        panic!("missing mathematical product bound")
    };
    let samples = [
        0,
        1,
        2,
        3,
        4,
        255,
        65520,
        65535,
        65536,
        0x7fff_ffff,
        0x8000_0000,
        u32::MAX,
    ];
    for a in samples {
        for b in samples {
            let safe = u64::from(a) * u64::from(b) <= u64::from(u32::MAX);
            assert_eq!(holds(premise, a, b), safe, "guard for {a} * {b}");
            assert_eq!(holds(conclusion, a, b), safe, "observation for {a} * {b}");
            assert_eq!(holds(product_bound, a, b), safe, "bound for {a} * {b}");
            assert_eq!(
                holds(native_guard, a, b),
                safe,
                "derived guard for {a} * {b}"
            );
        }
    }
    for b in samples.into_iter().filter(|b| *b > 1) {
        let last_safe = u32::MAX / b;
        for a in [last_safe, last_safe + 1] {
            let safe = a == last_safe;
            assert_eq!(holds(premise, a, b), safe, "quotient boundary {a} * {b}");
            assert_eq!(holds(conclusion, a, b), safe, "product boundary {a} * {b}");
            assert_eq!(holds(product_bound, a, b), safe, "bound boundary {a} * {b}");
            assert_eq!(
                holds(native_guard, a, b),
                safe,
                "derived boundary {a} * {b}"
            );
        }
    }
}

#[test]
fn uint32_integer_order_bridges_agree_with_unsigned_boundary_models() {
    fn machine(term: &Bitvector32Term, a: u32, b: u32) -> u32 {
        match term {
            Bitvector32Term::Variable(v) if *v == Variable(910) => a,
            Bitvector32Term::Variable(v) if *v == Variable(911) => b,
            Bitvector32Term::Constant(v) => *v,
            Bitvector32Term::BitwiseXor(left, right) => machine(left, a, b) ^ machine(right, a, b),
            _ => panic!("unexpected unsigned-order encoding {term:?}"),
        }
    }
    fn holds(p: &Proposition, a: u32, b: u32) -> bool {
        match p {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(left, right),
                true,
            ) => (machine(left, a, b) as i32) <= (machine(right, a, b) as i32),
            Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(left, right), true) => {
                let observe = |term: &IntegerTerm| {
                    let IntegerTerm::Machine(value) = term else {
                        panic!("expected exact observation")
                    };
                    assert_eq!(value.ty(), MachineIntegerType::UInt32);
                    num_bigint::BigInt::from(machine(value.value(), a, b))
                };
                observe(left) <= observe(right)
            }
            _ => panic!("unexpected bridge proposition {p:?}"),
        }
    }
    let left = Bitvector32Term::Variable(Variable(910));
    let right = Bitvector32Term::Variable(Variable(911));
    for theorem in [
        prove_uint32_less_equal_to_integer(left.clone(), right.clone()),
        prove_uint32_less_equal_of_to_integer(left.clone(), right.clone()),
    ] {
        let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
            panic!("missing guard")
        };
        for a in [
            0,
            1,
            255,
            65520,
            0x7fff_ffff,
            0x8000_0000,
            0x8000_0001,
            u32::MAX - 1,
            u32::MAX,
        ] {
            for b in [
                0,
                1,
                255,
                65520,
                0x7fff_ffff,
                0x8000_0000,
                0x8000_0001,
                u32::MAX - 1,
                u32::MAX,
            ] {
                assert_eq!(holds(premise, a, b), a <= b);
                assert_eq!(holds(conclusion, a, b), a <= b);
            }
        }
    }
}

#[test]
fn uint32_small_remainder_agrees_with_full_width_models() {
    let value = Bitvector32Term::Variable(Variable(920));
    let divisor = Bitvector32Term::Variable(Variable(921));
    let theorem = prove_uint32_remainder_of_lt(value.clone(), divisor.clone());
    let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
        panic!("missing strict unsigned guard")
    };
    assert_eq!(
        premise.as_ref(),
        &Proposition::ConditionIs(
            ConditionTerm::unsigned_less_than(value.clone(), divisor.clone()),
            true,
        )
    );
    assert_eq!(
        conclusion.as_ref(),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::unsigned_remainder(value, divisor),
                Bitvector32Term::Variable(Variable(920)),
            ),
            true,
        )
    );
    // Includes equality, zero divisors, and values on both sides of the sign bit.
    let samples = [
        0u32,
        1,
        2,
        255,
        65520,
        65521,
        0x7fff_ffff,
        0x8000_0000,
        u32::MAX - 1,
        u32::MAX,
    ];
    for value in samples {
        for divisor in samples {
            if value < divisor {
                assert_ne!(divisor, 0);
                assert_eq!(value % divisor, value);
            }
            if value == divisor && divisor != 0 {
                assert_ne!(value % divisor, value);
            }
        }
    }
}

#[test]
fn uint32_remainder_bound_agrees_with_full_width_models() {
    fn machine(term: &Bitvector32Term, value: u32, divisor: u32) -> u32 {
        match term {
            Bitvector32Term::Variable(v) if *v == Variable(920) => value,
            Bitvector32Term::Variable(v) if *v == Variable(921) => divisor,
            Bitvector32Term::Constant(v) => *v,
            Bitvector32Term::BitwiseXor(a, b) => {
                machine(a, value, divisor) ^ machine(b, value, divisor)
            }
            Bitvector32Term::UnsignedRemainder(a, b) => {
                machine(a, value, divisor) % machine(b, value, divisor)
            }
            _ => panic!("unexpected unsigned remainder term {term:?}"),
        }
    }
    let theorem = prove_uint32_remainder_less_than_divisor(
        Bitvector32Term::Variable(Variable(920)),
        Bitvector32Term::Variable(Variable(921)),
    );
    let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
        panic!("missing nonzero guard")
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(a, b), false) = premise.as_ref()
    else {
        panic!("wrong guard")
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(left, right), true) =
        conclusion.as_ref()
    else {
        panic!("wrong unsigned order")
    };
    for value in [
        0,
        1,
        65520,
        65521,
        0x7fff_ffff,
        0x8000_0000,
        0x8000_0001,
        u32::MAX - 1,
        u32::MAX,
    ] {
        for divisor in [
            0,
            1,
            2,
            4,
            65521,
            0x7fff_ffff,
            0x8000_0000,
            0x8000_0001,
            u32::MAX,
        ] {
            let guarded = machine(a, value, divisor) != machine(b, value, divisor);
            assert_eq!(guarded, divisor != 0);
            if guarded {
                assert!(u64::from(value) % u64::from(divisor) < u64::from(divisor));
                assert!(
                    (machine(left, value, divisor) as i32)
                        < (machine(right, value, divisor) as i32)
                );
            }
        }
    }
}

// Guarded bridges must agree with ordinary unsigned division at the sign
// boundary and maximum word, and must retain a false guard at zero divisors.
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
                        Bitvector32Term::Constant(value),
                        Bitvector32Term::Constant(divisor),
                    )
                } else {
                    prove_uint32_divide_to_integer(
                        Bitvector32Term::Constant(value),
                        Bitvector32Term::Constant(divisor),
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
                let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) =
                    conclusion.as_ref()
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
        let actual = match condition {
            ConditionTerm::Constant(value) => *value,
            ConditionTerm::IntegerNotEqual(a, b) => integer(a) != integer(b),
            ConditionTerm::IntegerLessEqual(a, b) => integer(a) <= integer(b),
            ConditionTerm::IntegerLessThan(a, b) => integer(a) < integer(b),
            ConditionTerm::IntegerEqual(a, b) => integer(a) == integer(b),
            ConditionTerm::Bitvector64Equal(a, b) => a.uint64_as_const() == b.uint64_as_const(),
            ConditionTerm::Bitvector64UnsignedLessEqual(a, b) => {
                a.uint64_as_const() <= b.uint64_as_const()
            }
            ConditionTerm::Bitvector64UnsignedLessThan(a, b) => {
                a.uint64_as_const() < b.uint64_as_const()
            }
            ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b) => {
                a.uint64_as_const() >= b.uint64_as_const()
            }
            _ => panic!("unexpected guard or equality"),
        };
        actual == *expected
    }
    for name in [
        "uint64_add_to_integer",
        "uint64_subtract_to_integer",
        "uint64_multiply_to_integer",
        "uint64_divide_to_integer",
        "uint64_remainder_to_integer",
        "uint64_less_than_to_integer",
        "uint64_less_than_implies_not_greater_equal",
        "uint64_less_equal_to_integer",
        "uint64_to_integer_less_equal_implies_less_equal",
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
                    Bitvector32Term::UInt64Constant(a),
                    Bitvector32Term::UInt64Constant(b),
                )
                .unwrap();
                let Proposition::Implies(guard, conclusion) = theorem.proposition() else {
                    panic!("missing guard");
                };
                let allowed = match name {
                    "uint64_add_to_integer" => a.checked_add(b).is_some(),
                    "uint64_subtract_to_integer" => a.checked_sub(b).is_some(),
                    "uint64_multiply_to_integer" => a.checked_mul(b).is_some(),
                    "uint64_divide_to_integer" | "uint64_remainder_to_integer" => b != 0,
                    "uint64_less_than_to_integer"
                    | "uint64_less_than_implies_not_greater_equal" => a < b,
                    _ => a <= b,
                };
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
                } else if !matches!(
                    name,
                    "uint64_divide_to_integer" | "uint64_remainder_to_integer"
                ) {
                    assert!(
                        !truth(conclusion),
                        "{name} must not erase wrapping or reverse order"
                    );
                }
            }
        }
    }
    assert!(
        prove_uint64_integer_bridge(
            "uint64_unknown",
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(0)
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
    let fact = |condition: ConditionTerm, value: bool| Proposition::ConditionIs(condition, value);

    // `0 <= e` and `e >= 0` over `Integer`, as `apply(uint32_to_integer_bounds(x))`
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
    let left = Box::new(Bitvector32Term::Variable(Variable(93_002)));
    let right = Box::new(Bitvector32Term::Variable(Variable(93_003)));
    let signed_below = fact(
        ConditionTerm::Bitvector64SignedLessThan(left.clone(), right.clone()),
        true,
    );
    let signed_above_mirrored = fact(
        ConditionTerm::Bitvector64SignedGreaterThan(right.clone(), left.clone()),
        true,
    );
    let signed_not_at_least = fact(
        ConditionTerm::Bitvector64SignedGreaterEqual(left.clone(), right.clone()),
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
        ConditionTerm::Bitvector64UnsignedGreaterThan(right.clone(), left.clone()),
        true,
    );
    assert!(!order_claim_equivalent(
        &signed_below,
        &unsigned_above_mirrored
    ));
    let unsigned_below = fact(
        ConditionTerm::Bitvector64UnsignedLessThan(left.clone(), right.clone()),
        true,
    );
    assert!(order_claim_equivalent(
        &unsigned_below,
        &unsigned_above_mirrored
    ));

    // Over the 32-bit signed order both judgments agree, as before.
    let below = fact(
        ConditionTerm::Bitvector32SignedLessThan(left.clone(), right.clone()),
        true,
    );
    let above_mirrored = fact(
        ConditionTerm::Bitvector32SignedGreaterThan(right, left),
        true,
    );
    assert!(condition_polarity_equivalent(&below, &above_mirrored));
    assert!(order_claim_equivalent(&below, &above_mirrored));
    assert_eq!(condition_polarity_forms(&below), order_claim_forms(&below));
}

#[test]
fn signed_64_branch_observation_bridges_match_boundary_models() {
    let left = Bitvector32Term::Variable(Variable(185101));
    let right = Bitvector32Term::Variable(Variable(185102));
    for strict in [false, true] {
        let theorem = if strict {
            prove_int64_less_than_to_integer(left.clone(), right.clone())
        } else {
            prove_int64_greater_equal_to_integer(left.clone(), right.clone())
        };
        let Proposition::Implies(premise, conclusion) = theorem.proposition() else {
            panic!("missing comparison premise");
        };
        let expected_native = if strict {
            ConditionTerm::int64_signed_less_than(left.clone(), right.clone())
        } else {
            ConditionTerm::int64_signed_greater_equal(left.clone(), right.clone())
        };
        assert_eq!(
            premise.as_ref(),
            &Proposition::ConditionIs(expected_native, true)
        );
        let observe = |v| IntegerTerm::from_machine(MachineIntegerType::Int64, v).unwrap();
        let expected_integer = if strict {
            ConditionTerm::IntegerLessThan(
                observe(left.clone()).into(),
                observe(right.clone()).into(),
            )
        } else {
            ConditionTerm::IntegerGreaterEqual(
                observe(left.clone()).into(),
                observe(right.clone()).into(),
            )
        };
        assert_eq!(
            conclusion.as_ref(),
            &Proposition::ConditionIs(expected_integer, true)
        );
        let values = [i64::MIN, -1, 0, 1, 8589934591, 8589934592, i64::MAX];
        for a in values {
            for b in values {
                let native = if strict { a < b } else { a >= b };
                let a = num_bigint::BigInt::from(a);
                let b = num_bigint::BigInt::from(b);
                let mathematical = if strict { a < b } else { b <= a };
                assert_eq!(native, mathematical);
            }
        }
    }
}

#[test]
fn bounded_byte_pointer_association_uses_checked_signed_addition() {
    let i = Bitvector32Term::Variable(Variable(198001));
    let left = PointerOffsetTerm::Add(
        Box::new(PointerOffsetTerm::scale_int32(i.clone(), 1)),
        Box::new(PointerOffsetTerm::Constant(4)),
    );
    let right = PointerOffsetTerm::scale_int32(
        Bitvector32Term::add(i.clone(), Bitvector32Term::Constant(4)),
        1,
    );
    let condition = ConditionTerm::pointer_offset_equal(left.clone(), right.clone());
    let goal = Proposition::ConditionIs(condition.clone(), true);
    let defined = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(i.clone(), Bitvector32Term::Constant(4)),
        false,
    );
    let facts = PureFactContext::new()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), i.clone()),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(i, Bitvector32Term::Constant(22200)),
            true,
        ))
        .assume_proposition(defined.clone());
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            std::slice::from_ref(&defined),
            &crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&defined)),
        )
        .is_ok()
    );
    assert_eq!(facts.decide(&condition), Some(true));
    assert!(
        crate::kernel::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
            &left, &right, &facts
        )
    );
    assert_eq!(facts.decide_condition_for_simp(&condition), Some(true));
    let proof = facts
        .derive_simp_proposition(&goal)
        .expect("exact bounded pointer association");
    assert!(proof.check(&facts));
}

#[test]
fn pointer_association_rejects_wrapping_and_incompatible_displacements() {
    use crate::kernel::proof::term_rewrite::TermRewrite;
    use std::collections::HashMap;
    let i = Bitvector32Term::Variable(Variable(198101));
    let j = Bitvector32Term::Variable(Variable(198102));
    let overflow = ConditionTerm::signed_add_overflows(i.clone(), j.clone());
    for width in [1, 4, 8, i64::from(u32::MAX)] {
        let left = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::scale_int32(i.clone(), width)),
            Box::new(PointerOffsetTerm::scale_int32(j.clone(), width)),
        );
        let right =
            PointerOffsetTerm::scale_int32(Bitvector32Term::add(i.clone(), j.clone()), width);
        let condition = ConditionTerm::pointer_offset_equal(left.clone(), right.clone());
        let reversed = ConditionTerm::pointer_offset_equal(right, left.clone());
        let no_wrap = HashMap::from([(overflow.clone(), false)]);
        let base = PointerOffsetTerm::Variable(Variable(198103));
        let based_left = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Add(
                Box::new(base.clone()),
                Box::new(PointerOffsetTerm::scale_int32(i.clone(), width)),
            )),
            Box::new(PointerOffsetTerm::scale_int32(j.clone(), width)),
        );
        let based_right = PointerOffsetTerm::Add(
            Box::new(base),
            Box::new(PointerOffsetTerm::scale_int32(
                Bitvector32Term::add(i.clone(), j.clone()),
                width,
            )),
        );
        let based = ConditionTerm::pointer_offset_equal(based_left.clone(), based_right);
        let different_base = ConditionTerm::pointer_offset_equal(
            based_left,
            PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Variable(Variable(198104))),
                Box::new(PointerOffsetTerm::scale_int32(
                    Bitvector32Term::add(i.clone(), j.clone()),
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
        let wrong_stride = ConditionTerm::pointer_offset_equal(
            left.clone(),
            PointerOffsetTerm::scale_int32(Bitvector32Term::add(i.clone(), j.clone()), width + 1),
        );
        let wrong_index = ConditionTerm::pointer_offset_equal(
            left,
            PointerOffsetTerm::scale_int32(
                Bitvector32Term::add(i.clone(), Bitvector32Term::Constant(5)),
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
    let max = Bitvector32Term::Constant(i32::MAX as u32);
    let exact = PointerOffsetTerm::Add(
        Box::new(PointerOffsetTerm::scale_int32(max.clone(), 1)),
        Box::new(PointerOffsetTerm::Constant(4)),
    );
    let wrapped =
        PointerOffsetTerm::scale_int32(Bitvector32Term::add(max, Bitvector32Term::Constant(4)), 1);
    let false_goal = ConditionTerm::pointer_offset_equal(exact, wrapped);
    assert_ne!(
        TermRewrite::for_conditions(&HashMap::new()).condition(&false_goal),
        ConditionTerm::Constant(true)
    );
}

#[test]
fn pointer_association_selected_guard_work_ignores_ambient_facts() {
    let i = Bitvector32Term::Variable(Variable(198201));
    let defined = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(i.clone(), Bitvector32Term::Constant(4)),
        false,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::scale_int32(i.clone(), 1)),
                Box::new(PointerOffsetTerm::Constant(4)),
            ),
            PointerOffsetTerm::scale_int32(
                Bitvector32Term::add(i, Bitvector32Term::Constant(4)),
                1,
            ),
        ),
        true,
    );
    let mut prior = None;
    for count in [0, 16, 64, 256, 1024] {
        let mut ambient = vec![defined.clone()];
        ambient.extend((0..count).map(|n| {
            Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(199000 + n)),
                    Bitvector32Term::Constant(n as u32),
                ),
                true,
            )
        }));
        let facts = crate::kernel::proof::ProofFacts::from_ordered(&ambient);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &goal,
                std::slice::from_ref(&defined),
                &facts,
            )
        });
        assert!(result.is_ok());
        assert!(work > 0);
        if let Some(old) = prior {
            assert_eq!(work, old);
        }
        prior = Some(work);
    }
}

#[test]
fn native_loadability_transport_pins_extent_domain_and_lifetime() {
    let base = Pointer {
        block: "native-region".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let live = CMemory::new().with_block("native-region", 8);
    let fact = |memory: CMemory, bytes, wide| Proposition::CMemoryLoadable {
        memory,
        base: base.clone(),
        bytes,
        wide,
    };
    let source = fact(live.clone(), Bitvector32Term::UInt64Constant(8), true);
    let context = PureFactContext::new().assume_proposition(source.clone());
    let written = live
        .clone()
        .store(base.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
    let goal = fact(written, Bitvector32Term::UInt64Constant(8), true);
    let proof = context
        .derive_atomic_proposition(&goal)
        .expect("writes preserve native liveness");
    assert!(proof.check(&context));
    assert_eq!(proof.context_premises(), vec![source]);
    for wrong in [
        fact(live.clone(), Bitvector32Term::UInt64Constant(9), true),
        fact(
            live.clone().with_block("native-region", 2),
            Bitvector32Term::UInt64Constant(8),
            true,
        ),
        fact(
            live.without_local_block(&base.block),
            Bitvector32Term::UInt64Constant(8),
            true,
        ),
    ] {
        assert!(context.derive_atomic_proposition(&wrong).is_none());
    }
    let native_count = Bitvector32Term::Variable(Variable(973_001));
    let narrow = PureFactContext::new().assume_proposition(fact(
        CMemory::new(),
        Bitvector32Term::UInt32From64(Box::new(native_count.clone())),
        false,
    ));
    assert!(
        narrow
            .derive_atomic_proposition(&fact(CMemory::new(), native_count, true,))
            .is_none(),
        "a low-word extent cannot establish the full native extent"
    );
    let external = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let live = CMemory::new()
        .with_heap_allocation_claim(external.clone(), Bitvector32Term::Constant(16))
        .unwrap();
    let dead = live
        .clone()
        .free_heap_block(&external, &PureFactContext::new())
        .unwrap();
    let external_fact = |memory| Proposition::CMemoryLoadable {
        memory,
        base: external.clone(),
        bytes: Bitvector32Term::UInt64Constant(8),
        wide: true,
    };
    let context = PureFactContext::new().assume_proposition(external_fact(live));
    assert!(
        context
            .derive_atomic_proposition(&external_fact(dead))
            .is_none()
    );
}

#[test]
fn native_loadability_prefix_coverage_retains_full_width_bounds() {
    let memory = CMemory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = |bytes| Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes,
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
            PureFactContext::new().assume_proposition(range(Bitvector32Term::UInt64Constant(held)));
        for requested in [0, 1, held, held.saturating_add(1)] {
            let goal = range(Bitvector32Term::UInt64Constant(requested));
            let proof = context.derive_atomic_proposition(&goal);
            assert_eq!(proof.is_some(), requested <= held, "{requested} <= {held}");
            if let Some(proof) = proof {
                assert!(proof.check(&context));
            }
        }
    }
    let held = Bitvector32Term::Variable(Variable(973_101));
    let requested = Bitvector32Term::Variable(Variable(973_102));
    let source = range(held.clone());
    let goal = range(requested.clone());
    let context = PureFactContext::new().assume_proposition(source.clone());
    assert!(context.derive_atomic_proposition(&goal).is_none());
    let bound = Proposition::ConditionIs(
        ConditionTerm::uint64_less_equal(requested.clone(), held.clone()),
        true,
    );
    let bounded = context.clone().assume_proposition(bound);
    let proof = bounded.derive_atomic_proposition(&goal).unwrap();
    assert!(proof.check(&bounded));
    assert!(
        !proof.check(&context),
        "the coverage bound must remain a premise"
    );
    let low_word_bound = Proposition::ConditionIs(
        ConditionTerm::unsigned_less_equal(
            Bitvector32Term::UInt32From64(Box::new(requested)),
            Bitvector32Term::UInt32From64(Box::new(held)),
        ),
        true,
    );
    assert!(
        context
            .assume_proposition(low_word_bound)
            .derive_atomic_proposition(&goal)
            .is_none()
    );
}

#[test]
fn native_loadability_prefix_coverage_preserves_lifetime_and_base() {
    let base = Pointer {
        block: "native-prefix".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let live = CMemory::new().with_block("native-prefix", 8);
    let range = |memory: CMemory, base: Pointer, bytes| Proposition::CMemoryLoadable {
        memory,
        base,
        bytes: Bitvector32Term::UInt64Constant(bytes),
        wide: true,
    };
    let context = PureFactContext::new().assume_proposition(range(live.clone(), base.clone(), 8));
    let written = live
        .clone()
        .store(base.clone(), CValue::Int32(Bitvector32Term::Constant(7)));
    assert!(
        context
            .derive_atomic_proposition(&range(written, base.clone(), 4))
            .unwrap()
            .check(&context)
    );
    for wrong in [
        range(live.clone().with_block("native-prefix", 2), base.clone(), 4),
        range(
            live.clone().without_local_block(&base.block),
            base.clone(),
            4,
        ),
        range(CMemory::new(), base.offset_by_bytes(8), 1),
    ] {
        assert!(context.derive_atomic_proposition(&wrong).is_none());
    }
    let external = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let allocated = CMemory::new()
        .with_heap_allocation_claim(external.clone(), Bitvector32Term::Constant(16))
        .unwrap();
    let retired = allocated
        .clone()
        .free_heap_block(&external, &PureFactContext::new())
        .unwrap();
    let context = PureFactContext::new().assume_proposition(range(allocated, external.clone(), 8));
    assert!(
        context
            .derive_atomic_proposition(&range(retired, external, 4))
            .is_none()
    );
}

#[test]
fn native_loadability_window_checks_offset_end_and_retirement() {
    let memory = CMemory::new();
    let source = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(17),
    };
    let range = |memory: CMemory, base: Pointer, bytes| Proposition::CMemoryLoadable {
        memory,
        base,
        bytes: Bitvector32Term::UInt64Constant(bytes),
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
            Pointer {
                block: source.block.clone(),
                offset: PointerOffsetTerm::Constant(17 + offset),
            },
            length,
        );
        let proof = context.derive_atomic_proposition(&goal);
        assert_eq!(
            proof.is_some(),
            expected,
            "offset {offset}, length {length}"
        );
        if let Some(proof) = proof {
            assert!(proof.check(&context));
        }
    }
    let root = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let large = 1u64 << 32;
    let goal_base = Pointer {
        block: root.block.clone(),
        offset: PointerOffsetTerm::Int64Scaled {
            value: Box::new(Bitvector32Term::UInt64Constant(large)),
            byte_width: 1,
            unsigned: true,
        },
    };
    let context =
        PureFactContext::new().assume_proposition(range(memory.clone(), root.clone(), large + 8));
    let goal = range(memory.clone(), goal_base.clone(), 8);
    assert!(
        context
            .derive_atomic_proposition(&goal)
            .unwrap()
            .check(&context)
    );
    assert!(
        context
            .derive_atomic_proposition(&range(memory, goal_base, 9))
            .is_none()
    );
    let live = CMemory::new()
        .with_heap_allocation_claim(root.clone(), Bitvector32Term::Constant(16))
        .unwrap();
    let dead = live
        .clone()
        .free_heap_block(&root, &PureFactContext::new())
        .unwrap();
    let context = PureFactContext::new().assume_proposition(range(live, root.clone(), 16));
    assert!(
        context
            .derive_atomic_proposition(&range(dead, root.offset_by_bytes(1), 4))
            .is_none()
    );
}

#[test]
fn native_loadability_window_requires_every_full_width_guard() {
    let memory = CMemory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let held = Bitvector32Term::Variable(Variable(973_201));
    let offset = Bitvector32Term::Variable(Variable(973_202));
    let requested = Bitvector32Term::Variable(Variable(973_203));
    let target = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Int64Scaled {
            value: Box::new(offset.clone()),
            byte_width: 1,
            unsigned: true,
        },
    };
    let source = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base,
        bytes: held.clone(),
        wide: true,
    };
    let goal = Proposition::CMemoryLoadable {
        memory,
        base: target,
        bytes: requested.clone(),
        wide: true,
    };
    let le =
        |left, right| Proposition::ConditionIs(ConditionTerm::uint64_less_equal(left, right), true);
    let guards = [
        le(
            offset.clone(),
            Bitvector32Term::UInt64Constant(i64::MAX as u64),
        ),
        le(offset.clone(), held.clone()),
        le(requested, Bitvector32Term::uint64_subtract(held, offset)),
    ];
    let full = guards.iter().cloned().fold(
        PureFactContext::new().assume_proposition(source.clone()),
        PureFactContext::assume_proposition,
    );
    let proof = full.derive_atomic_proposition(&goal).unwrap();
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
            context.derive_atomic_proposition(&goal).is_none(),
            "omitted guard {omitted}"
        );
    }
}

#[test]
fn native_loadability_window_query_work_ignores_unrelated_views() {
    let memory = CMemory::new();
    let root = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let target = root.offset_by_bytes(1);
    let mut expected = None;
    for count in [16, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: root.offset_by_bytes(4 * (index + 1)),
                bytes: Bitvector32Term::UInt64Constant(16),
                wide: true,
            });
        }
        context = context.assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: root.clone(),
            bytes: Bitvector32Term::UInt64Constant(16),
            wide: true,
        });
        // Construct the address index once before measuring hot queries.
        assert!(context.proves_native_memory_loadable(
            &memory,
            &root,
            &Bitvector32Term::UInt64Constant(16)
        ));
        let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                context.proves_native_memory_loadable(
                    &memory,
                    &target,
                    &Bitvector32Term::UInt64Constant(15),
                ),
                context.proves_native_memory_loadable(
                    &memory,
                    &target,
                    &Bitvector32Term::UInt64Constant(16),
                ),
            )
        });
        assert_eq!(answers, (true, false));
        if let Some(prior) = expected {
            assert_eq!(work, prior);
        } else {
            expected = Some(work);
        }
    }
}

#[test]
fn native_loadability_prefix_coverage_ignores_unrelated_addresses() {
    let memory = CMemory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let requested = Bitvector32Term::Variable(Variable(973_103));
    let mut expected = None;
    for count in [16, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: base.offset_by_bytes(4 * (index + 1)),
                bytes: Bitvector32Term::UInt64Constant(16),
                wide: true,
            });
        }
        context = context
            .assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: base.clone(),
                bytes: Bitvector32Term::UInt64Constant(16),
                wide: true,
            })
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::uint64_less_equal(
                    requested.clone(),
                    Bitvector32Term::UInt64Constant(16),
                ),
                true,
            ));
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                context.proves_native_memory_loadable(&memory, &base, &requested),
                context.proves_native_memory_loadable(
                    &memory,
                    &base,
                    &Bitvector32Term::UInt64Constant(17),
                ),
            )
        });
        assert_eq!(proved, (true, false));
        assert!(work > 0);
        if let Some(expected) = expected {
            assert_eq!(work, expected);
        } else {
            expected = Some(work);
        }
    }
}

#[test]
fn native_loadability_queries_do_not_visit_unrelated_addresses() {
    let memory = CMemory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut expected = None;
    for count in [16, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: Pointer {
                    block: base.block.clone(),
                    offset: PointerOffsetTerm::Constant(4 * (index + 1)),
                },
                bytes: Bitvector32Term::UInt64Constant(8),
                wide: true,
            });
        }
        context = context.assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::UInt64Constant(8),
            wide: true,
        });
        // Index construction is setup work. Repeated exact-range queries must
        // stay independent of the other addresses, even on a refusal.
        assert!(context.proves_native_memory_loadable(
            &memory,
            &base,
            &Bitvector32Term::UInt64Constant(8)
        ));
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.proves_native_memory_loadable(
                &memory,
                &base,
                &Bitvector32Term::UInt64Constant(9),
            )
        });
        assert!(!proved);
        if let Some(expected) = expected {
            assert_eq!(work, expected);
        } else {
            expected = Some(work);
        }
    }
}

#[test]
fn unsigned_u16_packing_bridges_match_disjoint_fields_and_retain_both_bounds() {
    use num_bigint::BigInt;
    fn word(term: &Bitvector32Term) -> u64 {
        match term {
            Bitvector32Term::Constant(value) => u64::from(*value),
            Bitvector32Term::UInt64Constant(value) => *value,
            Bitvector32Term::Int64Constant(value) => *value as u64,
            Bitvector32Term::BitwiseOr(a, b) | Bitvector32Term::UInt64BitwiseOr(a, b) => {
                word(a) | word(b)
            }
            Bitvector32Term::ShiftLeft(a, b) => {
                u64::from((word(a) as u32).wrapping_shl(word(b) as u32))
            }
            Bitvector32Term::UInt64ShiftLeft(a, b) => word(a).wrapping_shl(word(b) as u32),
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
            MachineIntegerType::UInt32 => Bitvector32Term::Constant(value as u32),
            MachineIntegerType::UInt64 => Bitvector32Term::UInt64Constant(value),
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
                    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(packed, exact), true) =
                        conclusion.as_ref()
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
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(0)
        )
        .is_none()
    );
    // Overlapping fields and a wrapping high field disprove the unguarded rule.
    assert_ne!(65536u32 | (1u32 << 16), 65536u32 + 65536u32);
    assert_ne!(u64::from(65536u32.wrapping_shl(16)), 65536u64 * 65536);
}

#[test]
fn uint32_unpacking_rules_retain_bounds_and_recover_all_word_bits() {
    fn evaluate(term: &Bitvector32Term) -> u32 {
        match term {
            Bitvector32Term::Constant(value) => *value,
            Bitvector32Term::BitwiseOr(left, right) => evaluate(left) | evaluate(right),
            Bitvector32Term::BitwiseAnd(left, right) => evaluate(left) & evaluate(right),
            Bitvector32Term::ShiftLeft(left, right) => evaluate(left).wrapping_shl(evaluate(right)),
            Bitvector32Term::LogicalShiftRight(left, right) => {
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
                    Bitvector32Term::Constant(low),
                    Bitvector32Term::Constant(high),
                ),
                prove_uint32_unpack_uint16_high(
                    Bitvector32Term::Constant(low),
                    Bitvector32Term::Constant(high),
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
                let identity_holds = match condition {
                    ConditionTerm::Constant(value) => *value,
                    ConditionTerm::Bitvector32Equal(extracted, original) => {
                        evaluate(extracted) == evaluate(original)
                    }
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
