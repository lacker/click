use super::*;

fn scalar(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}
fn offset(id: u64) -> PointerOffsetTerm {
    PointerOffsetTerm::Variable(Variable(id))
}
fn scaled(id: u64, width: i64) -> PointerOffsetTerm {
    PointerOffsetTerm::scale_int32(scalar(id), width)
}
fn nested(term: PointerOffsetTerm) -> PointerOffsetTerm {
    PointerOffsetTerm::Add(Box::new(term), Box::new(offset(90)))
}

#[test]
fn scaled_int32_congruence_propagates_early_and_late_into_addition_aliases() {
    for early in [false, true] {
        let mut graph = EqualityGraph::default();
        if early {
            graph.add_int32_equality(&scalar(1), &scalar(2));
        }
        graph.add_offset_equality(&nested(scaled(1, 4)), &offset(10));
        graph.add_offset_equality(&nested(scaled(3, 4)), &offset(11));
        let parent = graph.clone();
        let sibling = graph.clone();
        if !early {
            graph.add_int32_equality(&scalar(1), &scalar(2));
        }
        assert!(!graph.are_offsets_equal(&offset(10), &offset(11)));
        graph.add_int32_equality(&scalar(3), &scalar(2));
        assert!(graph.are_offsets_equal(&offset(11), &offset(10)));
        assert!(!parent.are_offsets_equal(&offset(10), &offset(11)));
        assert!(!sibling.are_offsets_equal(&offset(10), &offset(11)));
        assert!(!graph.are_offsets_equal(&scaled(1, 4), &scaled(3, 8)));
        for unsigned in [false, true] {
            let wide = |id| PointerOffsetTerm::Int64Scaled {
                value: Box::new(scalar(id)),
                byte_width: 4,
                unsigned,
            };
            assert!(!graph.are_offsets_equal(&scaled(1, 4), &wide(1)));
            assert!(!graph.are_offsets_equal(&wide(1), &wide(3)));
        }
    }
    let mut graph = EqualityGraph::default();
    graph.add_offset_equality(&scaled(1, 4), &scaled(2, 4));
    assert!(!graph.are_int32_equal(&scalar(1), &scalar(2)));
}

#[test]
fn scaled_int32_literals_join_folded_constants_without_overflow() {
    for value in [0, 1, u32::MAX, i32::MIN as u32] {
        for early in [false, true] {
            let mut graph = EqualityGraph::default();
            let literal = Bitvector32Term::Constant(value);
            if early {
                graph.add_int32_equality(&scalar(1), &literal);
            }
            graph.add_offset_equality(&nested(scaled(1, 4)), &offset(10));
            if !early {
                graph.add_int32_equality(&literal, &scalar(1));
            }
            let folded = PointerOffsetTerm::scale_int32(literal.clone(), 4);
            assert!(graph.are_offsets_equal(&offset(10), &nested(folded.clone())));
            let explicit = PointerOffsetTerm::Int32Scaled {
                value: Box::new(literal),
                byte_width: 4,
            };
            assert!(graph.are_offsets_equal(&explicit, &folded));
        }
    }
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&scalar(1), &Bitvector32Term::Constant(2));
    assert!(!graph.are_offsets_equal(&scaled(1, i64::MAX), &PointerOffsetTerm::Constant(-2)));
}

#[test]
fn scaled_int32_context_rebuilds_remove_only_unsupported_consequences() {
    let equality = ConditionTerm::equal(scalar(1), scalar(2));
    let explicit = ConditionTerm::pointer_offset_equal(scaled(2, 4), offset(10));
    let context = PureFactContext::new()
        .assume_condition(equality.clone(), true)
        .assume_condition(explicit.clone(), true);
    assert!(
        context
            .equality_graph
            .are_offsets_equal(&scaled(1, 4), &offset(10))
    );
    let withdrawn = context.without_exact_fact(&Proposition::ConditionIs(equality.clone(), true));
    assert!(
        !withdrawn
            .equality_graph
            .are_offsets_equal(&scaled(1, 4), &offset(10))
    );
    assert!(
        withdrawn
            .equality_graph
            .are_offsets_equal(&scaled(2, 4), &offset(10))
    );
    let restricted = context.restricted_to_facts(&[(equality, true)], &[]);
    assert!(
        restricted
            .equality_graph
            .are_offsets_equal(&scaled(1, 4), &scaled(2, 4))
    );
    assert!(
        !restricted
            .equality_graph
            .are_offsets_equal(&scaled(1, 4), &offset(10))
    );
}

#[test]
fn scaled_int32_late_merges_and_constant_evaluation_scale_with_affected_parents() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 1..=size {
            graph.add_offset_equality(&scaled(1, i as i64), &offset(10_000 + i));
            graph.add_offset_equality(&scaled(2, i as i64), &offset(20_000 + i));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.add_int32_equality(&scalar(1), &scalar(2));
                // The heavy class acquires a literal from a singleton.
                graph.add_int32_equality(&Bitvector32Term::Constant(3), &scalar(1));
                for i in 1..=size {
                    assert!(graph.are_offsets_equal(&offset(10_000 + i), &offset(20_000 + i)));
                    assert!(graph.are_offsets_equal(
                        &offset(10_000 + i),
                        &PointerOffsetTerm::Constant(3 * i as i64)
                    ));
                }
            })
        });
        assert!(work < 100 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn scaled_int32_forks_do_not_reindex_unaffected_parents() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 1..=size {
            graph.add_offset_equality(&scaled(1, i as i64), &offset(10_000 + i));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let mut branch = graph.clone();
                    branch.add_int32_equality(&scalar(20_000 + i), &scalar(1));
                    assert!(branch.are_offsets_equal(&scaled(20_000 + i, 1), &offset(10_001)));
                }
            })
        });
        assert!(work < 100 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 600 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        assert!(!graph.are_int32_equal(&scalar(20_000), &scalar(1)));
    }
}

#[test]
fn learning_a_literal_does_not_revisit_unrelated_boolean_parents() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for value in 0..size {
            graph.add_condition(
                &ConditionTerm::equal(scalar(1), Bitvector32Term::Constant(value as u32)),
                false,
            );
        }
        graph.add_offset_equality(&scaled(1, 4), &offset(10));
        let sibling = graph.clone();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_int32_equality(&scalar(1), &Bitvector32Term::Constant(2048));
            assert!(graph.are_offsets_equal(&offset(10), &PointerOffsetTerm::Constant(8192)));
        });
        assert!(!sibling.are_offsets_equal(&offset(10), &PointerOffsetTerm::Constant(8192)));
        assert!(graph.knows_condition(
            &ConditionTerm::equal(scalar(1), Bitvector32Term::Constant(0)),
            false
        ));
        samples.push((size, work));
    }
    let (smallest, base) = samples[0];
    for (size, work) in &samples {
        assert!(
            *work <= base + 8 * (size / smallest).ilog2() as usize,
            "literal learning: {samples:?}"
        );
    }
}
