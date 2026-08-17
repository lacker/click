use super::*;

#[test]
fn atomic_derivation_evidence_does_not_inline_multi_premise_payloads() {
    let one_step_envelope = std::mem::size_of::<SignedOrderDerivationStep>()
        + std::mem::align_of::<SignedOrderDerivationStep>();
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
    assert!(derivation.replay(&assumptions));

    let missing = PureFactContext::new().assume_proposition(less_equal);
    assert!(!derivation.replay(&missing));
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

#[test]
fn equality_graph_queries_share_one_condition_fact_index_build() {
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
    let expected_visits = assumptions.condition_facts.len();
    let _scope = assumptions.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();

    for term in &connected {
        assert!(assumptions.bitvector_terms_equal_from_facts(&root, term));
    }

    assert_eq!(
        PureFactContext::bitvector_equality_index_fact_visits(),
        expected_visits,
        "distinct equality queries must share one index build instead of rescanning ambient facts"
    );
}

#[test]
fn closed_forall_cache_accepts_only_kernel_proved_facts() {
    let variable = Variable(91_000);
    let reflexive = Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(variable),
                Bitvector32Term::Variable(variable),
            ),
            true,
        )),
    };
    let false_constant = Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(variable),
                Bitvector32Term::Constant(0),
            ),
            true,
        )),
    };

    assert!(
        crate::kernel::api::contract_certification::certification_proves_context_free_forall(
            &reflexive
        )
    );
    assert!(
        crate::kernel::api::contract_certification::certification_proves_context_free_forall(
            &reflexive
        ),
        "a previously proved closed fact should remain reusable"
    );
    assert!(
        !crate::kernel::api::contract_certification::certification_proves_context_free_forall(
            &false_constant
        ),
        "an assumption-dependent or false quantified fact must not enter the cache"
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
fn int32_strictly_positive_is_nonnegative_axiom_has_the_exact_implication() {
    let value = Bitvector32Term::Variable(Variable(90_023));
    let theorem = prove_int32_strictly_positive_is_nonnegative(value.clone());
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value, Bitvector32Term::Constant(0)),
        true,
    );

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(premise), Box::new(conclusion))
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
    let premise = Proposition::Not(Box::new(Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    )));
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
    let not_gt_premise = Proposition::Not(Box::new(Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
        true,
    )));
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

#[test]
fn pure_theorem_rewrite_certificate_issues_closed_authority() {
    let value_var = Variable(90_130);
    let left_var = Variable(90_131);
    let amount_var = Variable(90_132);
    let value = Bitvector32Term::Variable(value_var);
    let left = Bitvector32Term::Variable(left_var);
    let amount = Bitvector32Term::Variable(amount_var);
    let sum = Bitvector32Term::Add(Box::new(left.clone()), Box::new(amount.clone()));
    let equality = Proposition::ConditionIs(ConditionTerm::equal(value.clone(), sum.clone()), true);
    let requirements = vec![
        Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_add_overflows(left.clone(), amount.clone()),
                false,
            )),
            Box::new(equality.clone()),
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_subtract_overflows(value.clone(), amount.clone()),
            false,
        ),
    ];
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Subtract(Box::new(value), Box::new(amount)),
            left,
        ),
        true,
    );

    let authority = prove_universally_quantified_pure_implication_by_int32_rewrites(
        requirements,
        conclusion,
        vec![value_var, left_var, amount_var],
        vec![equality],
    );

    assert!(authority.is_some());
}

#[test]
fn pure_theorem_rewrite_certificate_rejects_unavailable_equality() {
    let value_var = Variable(90_140);
    let left_var = Variable(90_141);
    let amount_var = Variable(90_142);
    let value = Bitvector32Term::Variable(value_var);
    let left = Bitvector32Term::Variable(left_var);
    let amount = Bitvector32Term::Variable(amount_var);
    let equality = Proposition::ConditionIs(
        ConditionTerm::equal(
            value.clone(),
            Bitvector32Term::Add(Box::new(left.clone()), Box::new(amount.clone())),
        ),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Subtract(Box::new(value), Box::new(amount)),
            left,
        ),
        true,
    );

    let authority = prove_universally_quantified_pure_implication_by_int32_rewrites(
        Vec::new(),
        conclusion,
        vec![value_var, left_var, amount_var],
        vec![equality],
    );

    assert!(authority.is_none());
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
fn int32_le_and_not_lt_implies_eq_axiom_has_the_exact_implications() {
    let left = Bitvector32Term::Variable(Variable(90_032));
    let right = Bitvector32Term::Variable(Variable(90_033));
    let theorem = prove_int32_le_and_not_lt_implies_eq(left.clone(), right.clone());
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let not_lt_premise = Proposition::Not(Box::new(Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    )));
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
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), value.clone()),
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
        assert!(!crate::kernel::reasoning::with_memory_resolution_fuel(
            || { crate::kernel::reasoning::consume_memory_resolution_fuel() }
        ));
        assert!(!crate::kernel::reasoning::with_resource_prover_fuel(|| {
            crate::kernel::reasoning::consume_resource_prover_fuel()
        }));
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
    assert!(derivation.replay(&assumptions));
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
    assert!(derivation.replay(&assumptions));
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
    assert!(derivation.replay(&assumptions));
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
    assert!(derivation.replay(&assumptions));
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
    assert!(derivation.replay(&assumptions));
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
    assert!(derivation.replay(&assumptions));
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
    assert!(derivation.replay(&assumptions));
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
        assert!(derivation.replay(&assumptions));
    }
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
    assert!(nonnegative_derivation.replay(&positive_assumptions));

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
    assert!(decrease_derivation.replay(&positive_assumptions));

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
    assert!(bounded_derivation.replay(&bounded_assumptions));

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
        assert!(derivation.replay(&one_le_assumptions));
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
    assert!(derivation.replay(&assumptions));
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

    assert_replayable_derivation(&assumptions, &strict);
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
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_local),
                Box::new(owner_field.clone()),
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
            ),
            old_load,
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(fact);

    assert_replayable_derivation(&assumptions, &target);
}

#[test]
fn bounded_order_replay_ignores_unrelated_local_memory() {
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
    );
    let before_sparse_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before_sparse),
        Box::new(owner.clone()),
    );
    let after_load =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(owner));
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

    assert_replayable_derivation(&assumptions, &target);
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
    assert!(derivation.replay(&assumptions));
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
    }));
    assert!(assumptions.proves(&Proposition::CMemoryCanStore {
        memory,
        pointer,
        byte_width: 4,
    }));
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
    };
    let element = Proposition::CMemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
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
    };
    let selected = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(8),
    };
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(unrelated)
        .assume_proposition(selected.clone());
    let derivation = assumptions
        .derive_atomic_proposition(&target)
        .expect("the selected range should establish the element access");

    assert!(derivation.replay(&assumptions));
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
    };
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(index.clone()),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(range)
        .assume_condition(ConditionTerm::signed_less_equal(split, index.clone()), true)
        .assume_condition(ConditionTerm::signed_less_than(index, len), true);

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
    };
    let next_cell = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        bytes: Bitvector32Term::Constant(4),
    };
    let goal = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(12),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(prefix.clone())
        .assume_proposition(next_cell.clone());
    let derivation = assumptions
        .derive_atomic_proposition(&goal)
        .expect("an initialized next cell should extend the loadable prefix");
    assert!(derivation.replay(&assumptions));
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
    };
    let stored_assumptions = PureFactContext::new().assume_proposition(prefix.clone());
    let stored_derivation = stored_assumptions
        .derive_atomic_proposition(&stored_goal)
        .expect("a materialized next cell should extend the loadable prefix");
    assert!(stored_derivation.replay(&stored_assumptions));
    assert_eq!(stored_derivation.context_premises(), vec![prefix]);

    let gap = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(4)),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(goal.clone())
        .assume_proposition(gap);
    let too_wide = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: data,
        bytes: Bitvector32Term::Constant(16),
    };
    assert!(!assumptions.proves(&too_wide));
}

#[test]
fn field_derived_capacity_range_covers_a_shorter_live_prefix() {
    if skip_without_memory_dag() {
        return;
    }
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
    );
    let after_len = entry_memory
        .clone()
        .store(owner.clone(), CValue::Int32(len.clone()));
    let cap = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_len),
        Box::new(field(4)),
    );
    let after_cap = after_len
        .clone()
        .store(field(4), CValue::Int32(cap.clone()));
    let range_data_offset = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_cap),
        Box::new(field(8)),
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
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), len.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(len, cap), true);
    let target = Proposition::CMemoryLoadable {
        memory: entry_memory,
        base: entry_data.offset_by_int32_elements(index),
        bytes: Bitvector32Term::Constant(4),
    };

    assert!(
        assumptions.derive_atomic_proposition(&target).is_some(),
        "a field-derived capacity range must cover an entry-spelled live-prefix cell"
    );
}

#[test]
fn quantified_int32_fact_certifies_an_instantiated_load() {
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
    };

    assert!(assumptions.proves(&target));
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
fn quantified_int32_fact_certifies_its_complete_guarded_range() {
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
    };

    assert!(assumptions.proves(&target));
    assert!(!assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.with_block("other-state", 4),
        base: data.clone(),
        bytes: Bitvector32Term::multiply(length.clone(), Bitvector32Term::Constant(4)),
    }));
    assert!(!assumptions.proves(&Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: "other-data".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        bytes: Bitvector32Term::multiply(length, Bitvector32Term::Constant(4)),
    }));
}

#[test]
fn proposition_derivation_replay_requires_its_context() {
    let x = Bitvector32Term::Variable(Variable(86));
    let proposition = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x, Bitvector32Term::Constant(0)),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(proposition.clone());
    let derivation = assumptions
        .derive_simp_proposition(&proposition)
        .expect("exact fact should produce a derivation");

    assert!(derivation.replay(&assumptions));
    assert!(!derivation.replay(&PureFactContext::new()));
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

    assert!(derivation.replay(&assumptions));
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
fn forall_derivation_replay_shadows_ambient_uses_of_the_binder_id() {
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

    assert!(derivation.replay(&PureFactContext::new()));
    assert!(derivation.replay(&contaminated));
}

#[test]
fn finite_context_split_derivation_records_its_range_premises() {
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
    let assumptions = PureFactContext::new()
        .assume_proposition(lower.clone())
        .assume_proposition(upper.clone());
    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the singleton finite range should establish equality");

    assert!(derivation.replay(&assumptions));
    assert!(!derivation.replay(&PureFactContext::new()));
    let context = derivation.context_premises();
    assert!(context.contains(&lower));
    assert!(context.contains(&upper));
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

    assert!(derivation.replay(&assumptions));
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

#[test]
fn assumptions_split_small_finite_context_variable() {
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

    assert!(assumptions.proves(&proposition));
    assert_replayable_derivation(&assumptions, &proposition);
}

#[test]
fn finite_context_derivation_replays_under_a_narrower_range() {
    let j = Bitvector32Term::Variable(Variable(88));
    let broad = PureFactContext::new()
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
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(1)),
            true,
        )),
    );
    let derivation = broad
        .derive_proposition(&proposition)
        .expect("the broad two-value range should produce a finite proof");
    let narrow = broad.assume_condition(
        ConditionTerm::signed_less_than(j, Bitvector32Term::Constant(1)),
        true,
    );

    assert!(
        derivation.replay(&narrow),
        "a proof covering a finite range remains valid when later facts narrow that range"
    );
}

#[test]
fn proposition_derivation_composes_case_split_conjuncts() {
    let j = Bitvector32Term::Variable(Variable(187));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            true,
        );
    let finite_choice = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j, Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(187)),
                Bitvector32Term::Constant(1),
            ),
            true,
        )),
    );
    let proposition = Proposition::And(Box::new(finite_choice.clone()), Box::new(finite_choice));

    assert_replayable_derivation(&assumptions, &proposition);
}

#[test]
fn finite_forall_order_fact_participates_in_transitive_order_path() {
    let memory = CMemory::new();
    let indexed_load = |index| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::scale_int32(index, 4),
            }),
        )
    };
    let k = Variable(88);
    let k_bits = Bitvector32Term::Variable(k);
    let load_k = indexed_load(k_bits.clone());
    let load_0 = indexed_load(Bitvector32Term::Constant(0));
    let load_1 = indexed_load(Bitvector32Term::Constant(1));
    let load_2 = indexed_load(Bitvector32Term::Constant(2));
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

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(load_0, load_2),
        true,
    )));
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
    assert!(derivation.replay(&assumptions));
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

    let proposition = Proposition::Or(Box::new(x_is_one), Box::new(x_is_zero));
    assert!(assumptions.proves(&proposition));
    assert_replayable_derivation(&assumptions, &proposition);
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
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::multiply(length, Bitvector32Term::Constant(4)),
        });

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
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
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
        memory,
        base,
        bytes: Bitvector32Term::Constant(12),
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
    }));
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
    assert!(derivation.replay(&assumptions));
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
    assert!(derivation.replay(&assumptions));
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
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Normal(state),
        }
    );
}

#[test]
fn countdown_loop_body_preserves_nonnegative_invariant_symbolically() {
    let x = Variable(66);
    let x_bits = Bitvector32Term::Variable(x);
    let state = CState::new().with_local("x", int32(x_bits.clone()));
    let statement = c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1)));
    let invariant =
        ConditionTerm::signed_greater_equal(x_bits.clone(), Bitvector32Term::Constant(0));
    let condition =
        ConditionTerm::signed_greater_than(x_bits.clone(), Bitvector32Term::Constant(0));
    let post_invariant = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::Subtract(
                Box::new(x_bits.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(invariant.clone(), true)
        .assume_condition(condition.clone(), true);
    let theorem = prove_c_statement_executes_and_propositions(
        state.clone(),
        statement.clone(),
        assumptions,
        vec![post_invariant.clone()],
    )
    .expect("x > 0 should prove x - 1 executes and remains nonnegative");

    assert_eq!(
        theorem.proposition().peel_implications(),
        &proposition_and(
            Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Normal(CState::new().with_local(
                    "x",
                    int32(Bitvector32Term::Subtract(
                        Box::new(x_bits),
                        Box::new(Bitvector32Term::Constant(1)),
                    )),
                ),),
            },
            post_invariant,
        )
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
                        state: state.clone(),
                        statement: c_max_body(),
                        outcome: CStatementOutcome::Return {
                            value: int32(Bitvector32Term::Variable(b)),
                            state,
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
                        state: state.clone(),
                        statement: c_max_body(),
                        outcome: CStatementOutcome::Return {
                            value: int32(Bitvector32Term::Variable(a)),
                            state,
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
            left: CResource::Memory(memory_range(left.clone(), 0, 1)),
            right: CResource::Memory(memory_range(right.clone(), 0, 1)),
        });
    let _scope = assumptions.enter_id_scope();

    let work_for = |index: usize, query: fn(&Pointer, &Pointer, &PureFactContext) -> bool| {
        let tactic = crate::instrumentation::TacticEvent {
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
            };
            let (proved, work) =
                crate::instrumentation::measure_deterministic_work(|| assumptions.proves(&target));
            assert!(proved, "the guarded quantified fact certifies the load");
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
    let load = Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory), Box::new(cell));
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
/// so a strict order between them is a contradiction. Neither spelling is an
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
    let before = CMemory::new();
    let after = before
        .clone()
        .store(written.clone(), int32(Bitvector32Term::Constant(1)));
    let before_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(preserved.clone()),
    );
    let after_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(after.clone()),
        Box::new(preserved),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers: vec![written],
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
