use super::*;
use crate::kernel::*;

// Observe only this test's composite expansion/coverage input; release builds omit the hook
// and no retained contexts or extra clones in other tests.
thread_local! {
    static OBSERVED_CONTEXT: std::cell::RefCell<Option<Option<ResourceContext>>> = const { std::cell::RefCell::new(None) };
}

pub(super) fn record_context(context: &ResourceContext) {
    OBSERVED_CONTEXT.with(|cell| {
        if let Some(capture) = cell.borrow_mut().as_mut() {
            *capture = Some(context.clone());
        }
    });
}

fn projection_context(
    head: &CResourceFact,
    definition: &CCompositeResourceDefinition,
    memory: &CMemory,
    facts: &PureFactContext,
) -> ResourceContext {
    capture_context(|| {
        assert!(
            crate::kernel::functions::checked_composite_projection_evidence(
                head,
                std::slice::from_ref(definition),
                memory,
                facts,
            )
            .is_some(),
            "the viewed body must expand"
        );
    })
}

fn capture_context(operation: impl FnOnce()) -> ResourceContext {
    struct Restore(Option<Option<ResourceContext>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            OBSERVED_CONTEXT.with(|cell| *cell.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(OBSERVED_CONTEXT.with(|cell| cell.replace(Some(None))));
    operation();
    OBSERVED_CONTEXT.with(|cell| cell.borrow_mut().as_mut().unwrap().take().unwrap())
}

fn owned_frontier_context(
    head: &CResourceFact,
    definition: &CCompositeResourceDefinition,
    state: &CState,
    facts: &PureFactContext,
) -> ResourceContext {
    capture_context(|| {
        let frontier = crate::kernel::functions::checked_one_level_frontier(
            head,
            std::slice::from_ref(definition),
            state,
            facts,
        )
        .expect("the owned body must expand");
        assert_eq!(frontier.len(), 2);
        assert!(frontier.iter().all(CResourceFact::is_own));
    })
}

fn prior_child(context: ResourceContext, head: &CResourceFact) -> ResourceContext {
    let child = CResourceFact::own_memory(CMemoryRange::new(
        Pointer::symbolic(Variable(881_000)),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    context
        .without_exact_representation(head)
        .unwrap()
        .unchecked_with_fact(child)
}

fn fixture() -> (
    CResourceFact,
    CCompositeResourceDefinition,
    CMemory,
    PureFactContext,
    PureFactContext,
) {
    let at = |id| Pointer::symbolic(Variable(id));
    let (slot, middle, alias, target) = (at(881_000), at(881_001), at(881_002), at(881_003));
    let typed = |pointer| CValue::typed_pointer(pointer, CType::Int32Pointer);
    let head = CResourceFact::view_composite(
        "dependent_projection".into(),
        vec![
            typed(slot.clone()),
            typed(alias.clone()),
            typed(target.clone()),
        ],
    );
    let definition = CCompositeResourceDefinition::new(
        "dependent_projection",
        vec![
            c_parameter("slot", CType::Int32Pointer),
            c_parameter("alias", CType::Int32Pointer),
            c_parameter("target", CType::Int32Pointer),
        ],
        None,
        false,
        vec![
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("slot"),
                c_int32_literal(0),
                c_int32_literal(1),
            )),
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("target"),
                c_int32_literal(0),
                c_load(c_variable("alias")),
            )),
        ],
        Vec::new(),
    );
    let memory = CMemory::new()
        .with_block(slot.block.clone(), 4)
        .with_block(target.block, 8)
        .store(slot.clone(), int32(2u32));
    let sibling = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(882_000)),
                Bitvector32Term::Variable(Variable(882_001)),
            ),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(slot, middle.clone()), true);
    let branch = sibling
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(middle, alias), true);
    (head, definition, memory, branch, sibling)
}

#[test]
fn dependent_composite_projection_selects_the_prior_child_by_graph_address() {
    let (head, definition, memory, branch, sibling) = fixture();
    // Logical loads may bypass permission checks, so successful expansion
    // alone cannot establish that its resource index follows the graph.
    let context = projection_context(&head, &definition, &memory, &branch);
    let children = prior_child(context, &head);
    let alias = Pointer::symbolic(Variable(881_002));
    let entries = children.concrete_read_entries(&alias, 4, &branch);
    assert!(
        entries.is_some_and(|entries| entries.exact()),
        "projection context did not attach the prior child's graph address payload"
    );
    assert!(children.permits_memory_read(&alias, 4, &branch));
    assert!(!children.permits_memory_read(&alias, 4, &sibling));
    assert!(!children.permits_memory_read(&alias.offset_by_bytes(4), 4, &branch));
    assert!(!children.permits_memory_read(&alias, 12, &branch));
    let sibling_children = prior_child(
        projection_context(&head, &definition, &memory, &sibling),
        &head,
    );
    assert!(!sibling_children.permits_memory_read(&alias, 4, &sibling));
    // Querying another fork cannot contaminate either branch's payload.
    assert!(children.permits_memory_read(&alias, 4, &branch));
    assert!(sibling_children.facts().iter().all(CResourceFact::is_own));
}

#[test]
fn projection_evidence_still_requires_a_viewed_head_and_matching_definition() {
    let (head, definition, memory, facts, _) = fixture();
    let owned = CResourceFact::own(head.resource().clone());
    assert!(
        crate::kernel::functions::checked_composite_projection_evidence(
            &owned,
            std::slice::from_ref(&definition),
            &memory,
            &facts,
        )
        .is_none()
    );
    assert!(
        crate::kernel::functions::checked_composite_projection_evidence(
            &head,
            &[],
            &memory,
            &facts,
        )
        .is_none()
    );
}

#[test]
fn projection_context_attachment_does_not_scan_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (head, definition, memory, mut facts, _) = fixture();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(890_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(890_001 + i * 2)),
                ),
                true,
            );
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let context = projection_context(&head, &definition, &memory, &facts);
                let children = prior_child(context, &head);
                let alias = Pointer::symbolic(Variable(881_002));
                assert!(
                    children
                        .concrete_read_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(children.permits_memory_read(&alias, 4, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "projection scanned unrelated facts: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "projection rebuilt unrelated graph state: {samples:?}"
    );
}

#[test]
fn owned_composite_frontier_selects_the_prior_child_by_graph_address() {
    let (viewed, definition, memory, branch, sibling) = fixture();
    let head = CResourceFact::own(viewed.resource().clone());
    let state = CState::new().with_memory(memory);
    let context = owned_frontier_context(&head, &definition, &state, &branch);
    let children = prior_child(context, &head);
    let alias = Pointer::symbolic(Variable(881_002));
    assert!(
        children
            .concrete_read_entries(&alias, 4, &branch)
            .is_some_and(|entries| entries.exact()),
        "owned frontier context did not attach the prior child's graph address payload"
    );
    assert!(children.permits_memory_read(&alias, 4, &branch));
    assert!(!children.permits_memory_read(&alias, 4, &sibling));
    assert!(!children.permits_memory_read(&alias.offset_by_bytes(4), 4, &branch));
    assert!(!children.permits_memory_read(&alias, 12, &branch));
    let sibling_children = prior_child(
        owned_frontier_context(&head, &definition, &state, &sibling),
        &head,
    );
    assert!(!sibling_children.permits_memory_read(&alias, 4, &sibling));
    assert!(children.permits_memory_read(&alias, 4, &branch));
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn owned_frontier_attachment_ignores_unrelated_facts_and_caller_resources() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (viewed, definition, memory, mut facts, _) = fixture();
        let head = CResourceFact::own(viewed.resource().clone());
        let mut ambient = ResourceContext::new();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(891_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(891_001 + i * 2)),
                ),
                true,
            );
            ambient = ambient.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                Pointer::symbolic(Variable(895_000 + i)),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )));
        }
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(ambient);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let context = owned_frontier_context(&head, &definition, &state, &facts);
                assert_eq!(
                    context.facts(),
                    std::slice::from_ref(&head),
                    "frontier expansion must not import ambient authority"
                );
                let children = prior_child(context, &head);
                let alias = Pointer::symbolic(Variable(881_002));
                assert!(
                    children
                        .concrete_read_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(children.permits_memory_read(&alias, 4, &facts));
                assert!(!children.permits_memory_read(
                    &Pointer::symbolic(Variable(895_000)),
                    4,
                    &facts
                ));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "owned frontier scanned unrelated state: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "owned frontier rebuilt unrelated state: {samples:?}"
    );
}

fn coverage_context(
    available: Vec<CResourceFact>,
    required: &[CResourceFact],
    facts: &PureFactContext,
) -> (ResourceContext, Option<ResourceContext>) {
    let mut residual = None;
    let input = capture_context(|| {
        residual = crate::kernel::functions::checked_frontier_coverage(available, required, facts);
    });
    (input, residual)
}

fn coverage_piece(id: u64, start: u32, end: u32) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new(
        Pointer::symbolic(Variable(id)),
        Bitvector32Term::Constant(start),
        Bitvector32Term::Constant(end),
    ))
}

#[test]
fn frontier_coverage_selects_and_consumes_through_transitive_address_equality() {
    let (_, _, _, branch, sibling) = fixture();
    let owner = coverage_piece(881_000, 0, 1);
    let wanted = coverage_piece(881_002, 0, 1);
    let (input, residual) =
        coverage_context(vec![owner.clone()], std::slice::from_ref(&wanted), &branch);
    assert!(
        input
            .concrete_write_entries(&Pointer::symbolic(Variable(881_002)), 4, &branch)
            .is_some_and(|entries| entries.exact()),
        "frontier coverage bypassed the graph's whole-cell ownership payload"
    );
    assert!(
        residual
            .expect("equal addresses cover the requested piece")
            .is_empty()
    );
    assert!(
        coverage_context(vec![owner.clone()], std::slice::from_ref(&wanted), &sibling)
            .1
            .is_none()
    );
    assert!(
        coverage_context(
            vec![owner.clone()],
            &[coverage_piece(881_002, 0, 2)],
            &branch
        )
        .1
        .is_none()
    );
    assert!(
        coverage_context(vec![owner.clone()], &[wanted.clone(), wanted], &branch)
            .1
            .is_none(),
        "one occurrence cannot back the requested piece twice"
    );
    assert!(
        coverage_context(
            vec![CResourceFact::View(owner.resource().clone())],
            &[coverage_piece(881_002, 0, 1)],
            &branch
        )
        .1
        .is_none(),
        "a view must not supply owned coverage"
    );
    assert!(
        coverage_context(vec![owner], &[coverage_piece(881_002, 1, 2)], &branch)
            .1
            .is_none()
    );
}

#[test]
fn frontier_coverage_splits_ownership_and_preserves_the_input_snapshot() {
    let (_, _, _, facts, _) = fixture();
    let wanted = coverage_piece(881_002, 0, 1);
    let (input, residual) = coverage_context(
        vec![coverage_piece(881_000, 0, 3)],
        std::slice::from_ref(&wanted),
        &facts,
    );
    let residual = residual.expect("partial coverage splits the owner");
    assert_eq!(residual.facts(), &[coverage_piece(881_000, 1, 3)]);
    assert!(
        residual
            .clone()
            .without_fact_incrementally(&coverage_piece(881_002, 1, 3), &facts)
            .expect("the same graph-aware coverage path consumes the residual")
            .is_empty()
    );
    assert!(
        residual
            .without_fact_incrementally(&wanted, &facts)
            .is_none()
    );
    assert_eq!(
        input.facts(),
        &[coverage_piece(881_000, 0, 3)],
        "proof-local consumption must preserve the input snapshot"
    );
}

#[test]
fn frontier_coverage_does_not_scan_unrelated_equality_facts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (_, _, _, mut facts, _) = fixture();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(899_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(899_001 + i * 2)),
                ),
                true,
            );
        }
        let available = vec![coverage_piece(881_000, 0, 1)];
        let wanted = coverage_piece(881_002, 0, 1);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let (input, residual) =
                    coverage_context(available, std::slice::from_ref(&wanted), &facts);
                assert!(
                    input
                        .concrete_write_entries(&Pointer::symbolic(Variable(881_002)), 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(residual.unwrap().is_empty());
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "frontier coverage scanned unrelated facts: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "frontier coverage rebuilt unrelated graph state: {samples:?}"
    );
}

#[test]
fn resource_satisfaction_uses_transitive_addresses_without_restoring_consumed_ownership() {
    let (_, _, _, facts, sibling) = fixture();
    let original = ResourceContext::new()
        .try_compose_with_fact(coverage_piece(881_000, 0, 3), &facts)
        .unwrap();
    let residual = original
        .clone()
        .without_fact_incrementally(&coverage_piece(881_002, 0, 1), &facts)
        .unwrap();
    let wanted = coverage_piece(881_002, 1, 3);
    assert!(residual.satisfies_fact(&wanted, &facts));
    assert!(!residual.satisfies_fact(&wanted, &sibling));
    assert!(!residual.satisfies_fact(&coverage_piece(881_002, 0, 1), &facts));
    assert!(!residual.satisfies_fact(&coverage_piece(881_002, 1, 4), &facts));
    let alias = Pointer::symbolic(Variable(881_002));
    let shifted = CResourceFact::own_memory(CMemoryRange::new(
        alias.offset_by_elements(Bitvector32Term::Constant(1), 4),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    ));
    assert!(residual.satisfies_fact(&shifted, &facts));
    let bytes = |end| {
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            alias.clone(),
            Bitvector32Term::Constant(4),
            Bitvector32Term::Constant(end),
            1,
        ))
    };
    assert!(residual.satisfies_fact(&bytes(12), &facts));
    assert!(!residual.satisfies_fact(&bytes(13), &facts));
    assert!(residual.satisfies_fact(&CResourceFact::View(wanted.resource().clone()), &facts));
    assert!(original.satisfies_fact(&coverage_piece(881_002, 0, 3), &facts));
    assert_eq!(residual.facts(), &[coverage_piece(881_000, 1, 3)]);
    let viewed = ResourceContext::new()
        .try_compose_with_fact(
            CResourceFact::View(coverage_piece(881_000, 1, 3).resource().clone()),
            &facts,
        )
        .unwrap();
    assert!(!viewed.satisfies_fact(&wanted, &facts));
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn resource_satisfaction_does_not_scan_unrelated_resources_or_equalities() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (_, _, _, mut facts, _) = fixture();
        let mut available = vec![coverage_piece(881_000, 1, 3)];
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(899_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(899_001 + i * 2)),
                ),
                true,
            );
            available.push(coverage_piece(895_000 + i, 0, 1));
        }
        let context = ResourceContext::new()
            .try_compose_with_facts(available, &facts)
            .unwrap();
        let wanted = coverage_piece(881_002, 1, 3);
        let consumed = coverage_piece(881_002, 0, 1);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(context.satisfies_fact(&wanted, &facts));
                assert!(!context.satisfies_fact(&consumed, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "resource satisfaction scanned unrelated state: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "resource satisfaction rebuilt unrelated state: {samples:?}"
    );
}

#[test]
fn framing_producer_publishes_opened_ownership_before_alias_lookup() {
    let (head, definition, memory, facts, sibling) = fixture();
    let head = CResourceFact::own(head.resource().clone());
    let residual = ResourceContext::new()
        .try_compose_with_fact(head, &facts)
        .unwrap();
    let state = CState::new()
        .with_memory(memory)
        .with_resource_context(residual.clone());
    let kept = crate::kernel::functions::call_kept_ownership(
        &residual,
        std::slice::from_ref(&definition),
        &state,
        &facts,
    );
    let opened = kept.opened_resources_for_test();
    let alias = Pointer::symbolic(Variable(881_002));
    assert!(
        opened
            .concrete_write_entries(&alias, 4, &facts)
            .is_some_and(|entries| entries.exact()),
        "the framing producer did not publish its selected owned ranges"
    );
    assert!(opened.satisfies_fact(&coverage_piece(881_002, 0, 1), &facts));
    assert!(!opened.satisfies_fact(&coverage_piece(881_002, 0, 1), &sibling));
    assert_eq!(residual.facts().len(), 1);
}

#[test]
fn fresh_resource_publication_tracks_late_equalities_and_persistent_deltas() {
    let (_, _, _, branch, sibling) = fixture();
    let original = ResourceContext::new_with_equalities(&sibling)
        .unchecked_with_fact(coverage_piece(881_000, 0, 1));
    let alias = Pointer::symbolic(Variable(881_002));
    assert!(!original.satisfies_fact(&coverage_piece(881_002, 0, 1), &sibling));
    assert!(
        original
            .concrete_write_entries(&alias, 4, &branch)
            .is_some_and(|entries| entries.exact())
    );
    let descendant = original
        .clone()
        .unchecked_with_fact(coverage_piece(881_003, 0, 1));
    let consumed = descendant
        .without_fact_incrementally(&coverage_piece(881_002, 0, 1), &branch)
        .unwrap();
    assert!(!consumed.satisfies_fact(&coverage_piece(881_002, 0, 1), &branch));
    assert!(consumed.satisfies_fact(&coverage_piece(881_003, 0, 1), &branch));
    assert_eq!(original.facts(), &[coverage_piece(881_000, 0, 1)]);
    assert!(!original.satisfies_fact(&coverage_piece(881_002, 0, 1), &sibling));
}

#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn fresh_and_framing_publication_do_not_scan_ambient_inputs() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (head, definition, memory, mut facts, _) = fixture();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(899_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(899_001 + i * 2)),
                ),
                true,
            );
        }
        let head = CResourceFact::own(head.resource().clone());
        let residual = ResourceContext::new()
            .try_compose_with_fact(head.clone(), &facts)
            .unwrap();
        let ambient = residual
            .clone()
            .try_compose_with_facts((0..size).map(|i| coverage_piece(895_000 + i, 0, 1)), &facts)
            .unwrap();
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(ambient);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let fresh = ResourceContext::new_with_equalities(&facts)
                    .unchecked_with_fact(coverage_piece(881_000, 0, 1));
                let alias = Pointer::symbolic(Variable(881_002));
                assert!(
                    fresh
                        .concrete_write_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                let kept = crate::kernel::functions::call_kept_ownership(
                    &residual,
                    std::slice::from_ref(&definition),
                    &state,
                    &facts,
                );
                let opened = kept.opened_resources_for_test();
                assert!(
                    opened
                        .concrete_write_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert_eq!(
                    opened.facts().len(),
                    2,
                    "ambient authority must not enter the frontier"
                );
                assert!(!opened.satisfies_fact(&coverage_piece(895_000, 0, 1), &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "publication scanned unrelated graph/resource input: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "publication rebuilt unrelated state: {samples:?}"
    );
}
