use super::*;
fn var(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}
fn add(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    Bitvector32Term::Add(Box::new(left), Box::new(right))
}
fn eq(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    ConditionTerm::equal(left, right)
}

#[test]
fn int32_addition_closes_both_operands_early_and_late_through_scaled_offsets() {
    for early in [false, true] {
        let mut graph = EqualityGraph::default();
        if early {
            graph.add_int32_equality(&var(1), &var(2));
        }
        let left = add(add(var(1), var(3)), var(5));
        let right = add(add(var(2), var(4)), var(5));
        graph.add_int32_equality(&left, &var(10));
        graph.add_int32_equality(&right, &var(11));
        let offset = |v| PointerOffsetTerm::scale_int32(v, 4);
        let alias = |i| PointerOffsetTerm::Variable(Variable(i));
        graph.add_offset_equality(&offset(left), &alias(20));
        graph.add_offset_equality(&offset(right), &alias(21));
        let parent = graph.clone();
        let sibling = graph.clone();
        if !early {
            graph.add_int32_equality(&var(1), &var(2));
        }
        assert!(!graph.are_int32_equal(&var(10), &var(11)));
        graph.add_int32_equality(&var(4), &var(3));
        assert!(graph.are_int32_equal(&var(11), &var(10)));
        assert!(graph.are_offsets_equal(&alias(20), &alias(21)));
        for unchanged in [parent, sibling] {
            assert!(!unchanged.are_int32_equal(&var(10), &var(11)));
            assert!(!unchanged.are_offsets_equal(&alias(20), &alias(21)));
        }
    }
}

#[test]
fn int32_addition_folds_literal_classes_using_bitvector_semantics() {
    for (a, b) in [(1u32, 2u32), (u32::MAX, 1), (i32::MAX as u32, 1)] {
        for early in [false, true] {
            let mut graph = EqualityGraph::default();
            if early {
                graph.add_int32_equality(&var(1), &Bitvector32Term::Constant(a));
                graph.add_int32_equality(&var(2), &Bitvector32Term::Constant(b));
            }
            graph.add_int32_equality(&add(var(1), var(2)), &var(10));
            if !early {
                graph.add_int32_equality(&Bitvector32Term::Constant(a), &var(1));
                graph.add_int32_equality(&Bitvector32Term::Constant(b), &var(2));
            }
            let result = Bitvector32Term::Constant(a.wrapping_add(b));
            assert!(graph.are_int32_equal(&var(10), &result));
            assert!(graph.are_int32_equal(
                &add(Bitvector32Term::Constant(a), Bitvector32Term::Constant(b)),
                &result
            ));
            assert!(!graph.are_int32_equal(
                &var(10),
                &Bitvector32Term::Constant(a.wrapping_add(b).wrapping_add(1))
            ));
        }
    }
}

#[test]
fn int32_addition_does_not_cancel_commute_or_merge_other_sorts() {
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&add(var(1), var(3)), &add(var(2), var(3)));
    assert!(!graph.are_int32_equal(&var(1), &var(2)));
    assert!(!graph.are_int32_equal(&add(var(1), var(3)), &add(var(3), var(1))));
    graph.add_int32_equality(&var(1), &var(2));
    let wide = |v| Bitvector32Term::Int64Add(Box::new(v), Box::new(var(3)));
    assert!(!graph.are_int32_equal(&wide(var(1)), &wide(var(2))));
    assert!(!graph.are_int32_equal(&add(var(1), var(3)), &wide(var(1))));
    let scalar_offset = PointerOffsetTerm::scale_int32(add(var(1), var(3)), 4);
    let offset_sum = PointerOffsetTerm::Add(
        Box::new(PointerOffsetTerm::Variable(Variable(1))),
        Box::new(PointerOffsetTerm::Variable(Variable(3))),
    );
    assert!(!graph.are_offsets_equal(&scalar_offset, &offset_sum));
}

#[test]
fn int32_addition_context_rebuilds_preserve_only_supported_equalities() {
    let premise = eq(var(1), var(2));
    let explicit = eq(add(var(2), var(3)), var(10));
    let context = PureFactContext::new()
        .assume_condition(premise.clone(), true)
        .assume_condition(explicit.clone(), true);
    let query = add(var(1), var(3));
    assert!(context.equality_graph.are_int32_equal(&query, &var(10)));
    let withdrawn = context.without_exact_fact(&Proposition::ConditionIs(premise.clone(), true));
    assert!(!withdrawn.equality_graph.are_int32_equal(&query, &var(10)));
    assert!(
        withdrawn
            .equality_graph
            .are_int32_equal(&add(var(2), var(3)), &var(10))
    );
    let restricted = context.restricted_to_facts(&[(premise, true)], &[]);
    assert!(
        restricted
            .equality_graph
            .are_int32_equal(&query, &add(var(2), var(3)))
    );
    assert!(!restricted.equality_graph.are_int32_equal(&query, &var(10)));
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn int32_addition_late_merge_and_fork_work_is_indexed() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_int32_equality(&add(var(1), var(100 + i)), &var(10_000 + i));
            graph.add_int32_equality(&add(var(2), var(100 + i)), &var(20_000 + i));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.add_int32_equality(&var(1), &var(2));
                for i in 0..size {
                    assert!(graph.are_int32_equal(&var(10_000 + i), &var(20_000 + i)));
                }
            })
        });
        assert!(work < 100 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let mut branch = graph.clone();
                    branch.add_int32_equality(&var(30_000 + i), &var(1));
                    assert!(branch.are_int32_equal(&add(var(30_000 + i), var(100)), &var(10_000)));
                }
            })
        });
        assert!(work < 200 * size as usize, "size={size}, fork work={work}");
        assert!(
            map_work < 1000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, fork map work={map_work}"
        );
    }
}

#[test]
fn int32_addition_nested_registration_and_literal_propagation_scale() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut term = var(1);
        for _ in 0..size {
            term = add(term, Bitvector32Term::Constant(1));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                graph.add_int32_equality(&term, &var(10));
                graph.add_int32_equality(&var(1), &Bitvector32Term::Constant(0));
                assert!(graph.are_int32_equal(&var(10), &Bitvector32Term::Constant(size as u32)));
            })
        });
        assert!(work < 200 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}
