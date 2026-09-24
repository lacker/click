//! Deterministic scaling regressions for resource-context validity.
//!
//! A call composes its ensured resources into the caller's frame and checks
//! that the result is still a partition. Only indexed candidates can violate
//! that — an identity held twice, a block owning two ranges, a base an exact
//! pointer equality joins to another block — so the check must cost work
//! logarithmic in the caller's unrelated allocations and instances rather
//! than proportional to them. Each test measures charged deterministic work
//! at four sizes and prints the numbers in its assertion messages.

use super::*;

const SIZES: [usize; 4] = [16, 64, 256, 1024];

/// The identity of the block the measured operation targets; the unrelated
/// ones take identities below it.
const TARGET_HEAP: u64 = 1_000_000;

fn heap_base(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::Heap(identity),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn owned_range(base: Pointer, start: u32, end: u32) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new(
        base,
        Bitvector32Term::Constant(start),
        Bitvector32Term::Constant(end),
    ))
}

fn owned_instance(identity: u64) -> CResourceFact {
    let schema = ResourceFieldSchema::new(vec![(
        "revision".into(),
        ResourceFieldType::C(CType::Int32),
    )])
    .unwrap();
    CResourceFact::own(CResource::Instance(
        ResourceInstance::new(
            Variable(identity),
            "counter".into(),
            Vec::new().into(),
            schema,
            vec![int32(0).into()].into(),
        )
        .unwrap(),
    ))
}

/// A caller frame holding `unrelated` heap allocations, each owning one
/// range, and as many unrelated resource instances, beside a target block
/// owning two adjacent ranges.
fn frame_with_unrelated_allocations(unrelated: usize) -> ResourceContext {
    ResourceContext::new()
        .unchecked_with_facts((0..unrelated).flat_map(|index| {
            [
                owned_range(heap_base(index as u64 + 1), 0, 4),
                owned_instance(TARGET_HEAP + 1 + index as u64),
            ]
        }))
        .unchecked_with_facts([
            owned_range(heap_base(TARGET_HEAP), 0, 4),
            owned_range(heap_base(TARGET_HEAP), 4, 8),
        ])
}

fn pointer_equal(left: Pointer, right: Pointer) -> ConditionTerm {
    ConditionTerm::PointerEqual(Box::new(left), Box::new(right))
}

fn symbolic_base(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::Symbolic(Variable(identity)),
        offset: PointerOffsetTerm::Constant(0),
    }
}

/// One exact equality naming the target block, so the cross-block alias walk
/// has a candidate to visit.
fn assumptions_aliasing_the_target() -> PureFactContext {
    PureFactContext::new().assume_condition(
        pointer_equal(heap_base(TARGET_HEAP), symbolic_base(2 * TARGET_HEAP)),
        true,
    )
}

fn log2(size: usize) -> f64 {
    (size as f64).log2()
}

fn assert_constant_plus_log_growth(what: &str, samples: &[(usize, usize)], slope: f64) {
    eprintln!("{what} (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    for (size, work) in samples {
        let allowed = base_work as f64 + slope * (log2(*size) - log2(smallest));
        assert!(
            (*work as f64) <= allowed,
            "{what}: {size} unrelated resources charged {work} units, above {allowed:.1} \
             (constant plus {slope}·log2 growth): {samples:?}"
        );
    }
}

#[test]
fn validity_is_logarithmic_in_unrelated_allocations() {
    let mut samples = Vec::new();
    for size in SIZES {
        let frame = frame_with_unrelated_allocations(size);
        let assumptions = assumptions_aliasing_the_target();
        let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.validity_error(&assumptions)
        });
        assert_eq!(error, None, "the frame is a partition");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("validity of a frame", &samples, 4.0);
}

#[test]
fn ensured_resource_composition_is_logarithmic_in_unrelated_allocations() {
    let mut samples = Vec::new();
    for size in SIZES {
        let frame = frame_with_unrelated_allocations(size);
        let assumptions = assumptions_aliasing_the_target();
        let ensured = owned_range(heap_base(TARGET_HEAP), 8, 12);
        let (composed, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame
                .clone()
                .try_compose_with_facts_delaying_normalization_with_occurrences(
                    [ensured.clone()],
                    &assumptions,
                )
        });
        let (composed, inserted) = composed.expect("the ensured range is disjoint");
        assert_eq!(inserted.len(), 1);
        assert!(composed.contains_exact_representation(&ensured));
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("composing one ensured range", &samples, 4.0);
}

/// The cross-block walk is driven from the smaller of the context's bases and
/// the equalities, so many unrelated equalities beside a small frame cost as
/// little as many unrelated allocations beside a few equalities.
#[test]
fn validity_is_logarithmic_in_unrelated_pointer_equalities() {
    let mut samples = Vec::new();
    for size in SIZES {
        let frame = frame_with_unrelated_allocations(2);
        let assumptions = (0..size).fold(assumptions_aliasing_the_target(), |facts, index| {
            facts.assume_condition(
                pointer_equal(
                    symbolic_base(3 * TARGET_HEAP + 2 * index as u64),
                    symbolic_base(3 * TARGET_HEAP + 2 * index as u64 + 1),
                ),
                true,
            )
        });
        let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.validity_error(&assumptions)
        });
        assert_eq!(error, None, "the frame is a partition");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("validity beside unrelated equalities", &samples, 4.0);
}

/// Skipping blocks and bases that hold no pair must not skip a violation:
/// each kind is still found beside many unrelated resources, from either
/// side of the alias walk, and reports the same pair.
#[test]
fn indexed_validity_still_finds_every_violation_kind() {
    for size in [0, 3, 64] {
        let frame = frame_with_unrelated_allocations(size);
        let none = PureFactContext::new();

        let overlapping =
            frame
                .clone()
                .unchecked_with_fact(owned_range(heap_base(TARGET_HEAP), 2, 6));
        assert!(
            matches!(
                overlapping.validity_error(&none),
                Some(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
            ),
            "a same-block overlap beside {size} allocations"
        );

        let duplicate = frame
            .clone()
            .unchecked_with_fact(owned_instance(TARGET_HEAP + 1));
        let expected_duplicate = if size == 0 {
            None
        } else {
            Some(ResourceContextValidityError::DuplicateOwnedResourceFact(
                owned_instance(TARGET_HEAP + 1),
            ))
        };
        assert_eq!(
            duplicate.validity_error(&none),
            expected_duplicate,
            "a duplicate instance beside {size} allocations"
        );

        let invalid_access =
            CResourceFact::View(owned_instance(2 * TARGET_HEAP).resource().clone());
        assert_eq!(
            frame
                .clone()
                .unchecked_with_fact(invalid_access.clone())
                .validity_error(&none),
            Some(ResourceContextValidityError::InvalidInstanceAccess(
                invalid_access
            )),
            "an instance view beside {size} allocations"
        );

        // A second block owning the target's first range, joined to it by an
        // exact equality: once with fewer equalities than bases, once with
        // more, so both drivers of the alias walk find the pair.
        let other = heap_base(3 * TARGET_HEAP);
        let aliased = frame
            .clone()
            .unchecked_with_fact(owned_range(other.clone(), 0, 4));
        let joined = PureFactContext::new()
            .assume_condition(pointer_equal(heap_base(TARGET_HEAP), other.clone()), true);
        let crowded = (0..2 * size + 8).fold(joined.clone(), |facts, index| {
            facts.assume_condition(
                pointer_equal(
                    symbolic_base(4 * TARGET_HEAP + 2 * index as u64),
                    symbolic_base(4 * TARGET_HEAP + 2 * index as u64 + 1),
                ),
                true,
            )
        });
        for assumptions in [&joined, &crowded] {
            assert!(
                matches!(
                    aliased.validity_error(assumptions),
                    Some(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
                ),
                "an aliased cross-block overlap beside {size} allocations"
            );
        }
        assert_eq!(aliased.validity_error(&none), None);
    }
}

/// A field-bearing `suffix(p)` whose owned range starts at its own `start`
/// field, and a parent `holder(p)` whose field `at` sets that child's
/// `start` and whose child is passed `p`: the body shapes of a plain-field
/// endpoint and a field-to-field child equation.
fn field_endpoint_definitions() -> Vec<CCompositeResourceDefinition> {
    let suffix_schema =
        ResourceFieldSchema::new(vec![("start".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let holder_schema =
        ResourceFieldSchema::new(vec![("at".into(), ResourceFieldType::C(CType::Int32))]).unwrap();
    let suffix = CCompositeResourceDefinition::new(
        "suffix",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment {
            base: c_variable("p"),
            start: c_variable("start"),
            end: c_int32_literal(8),
            element_width: 4,
            guard: None,
        })],
        vec![],
    )
    .with_instance_schema(Some(suffix_schema));
    let holder = CCompositeResourceDefinition::new(
        "holder",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![],
        vec![],
    )
    .with_children(vec![CResourceChildSpec {
        name: "rest".into(),
        resource: "suffix".into(),
        binding: Variable(90),
        arguments: vec![c_variable("p")],
        field_bindings: vec![CResourceChildField::Parent(0)],
    }])
    .with_instance_schema(Some(holder_schema));
    // Definitions are looked up by binary search on their names.
    vec![holder, suffix]
}

fn field_endpoint_instance(name: &str, field: &str, identity: u64) -> ResourceInstance {
    ResourceInstance::new(
        Variable(identity),
        name.into(),
        vec![CValue::pointer(heap_base(TARGET_HEAP)).into()].into(),
        ResourceFieldSchema::new(vec![(field.into(), ResourceFieldType::C(CType::Int32))]).unwrap(),
        vec![int32(2).into()].into(),
    )
    .unwrap()
}

#[test]
fn field_endpoint_fold_and_unfold_ignore_unrelated_resources() {
    let definitions = field_endpoint_definitions();
    let (holder, suffix) = (&definitions[0], &definitions[1]);
    let mut samples = Vec::new();
    for size in SIZES {
        let parent = field_endpoint_instance("holder", "at", 2 * TARGET_HEAP);
        let child = field_endpoint_instance("suffix", "start", 2 * TARGET_HEAP + 1);
        let frame = ResourceContext::new()
            .unchecked_with_facts((0..size).flat_map(|index| {
                [
                    owned_range(heap_base(index as u64 + 1), 0, 4),
                    owned_instance(TARGET_HEAP + 1 + index as u64),
                ]
            }))
            .unchecked_with_facts([CResourceFact::own(CResource::Instance(parent.clone()))]);
        let state = CState::new().with_resource_context(frame);
        let assumptions = PureFactContext::new();
        let children = vec![("rest".to_string(), child.identity)];
        let (round_trip, work) = crate::instrumentation::measure_deterministic_work(|| {
            let rewrite = |state: &CState,
                           instance: &ResourceInstance,
                           definition: &CCompositeResourceDefinition,
                           unfold: bool,
                           children: Option<&[(String, Variable)]>| {
                crate::kernel::rewrite_resource_instance_selecting_children(
                    state,
                    instance,
                    definition,
                    &definitions,
                    &assumptions,
                    unfold,
                    children,
                )
                .map(|rewrite| rewrite.state)
            };
            let open = rewrite(&state, &parent, holder, true, Some(&children))?;
            let cells = rewrite(&open, &child, suffix, true, None)?;
            let child_again = rewrite(&cells, &child, suffix, false, None)?;
            rewrite(&child_again, &parent, holder, false, Some(&children))
        });
        let closed = round_trip.unwrap_or_else(|refusal| {
            panic!(
                "the field-endpoint round trip should succeed: {}",
                refusal.describe()
            )
        });
        assert_eq!(
            closed.resources.owned_instance(parent.identity),
            Some(&parent)
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("field-endpoint fold and unfold", &samples, 16.0);
}

/// A field-bearing `window(p)` whose unconditional, unmatched body owns
/// `cells` one-element ranges of `p`, the first starting at its own `start`
/// field: the body shape whose cells a folded instance publishes as read
/// authority to its sibling contract clauses.
fn window_definitions(cells: u32) -> Vec<CCompositeResourceDefinition> {
    let schema =
        ResourceFieldSchema::new(vec![("start".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let contains = (0..cells)
        .map(|cell| {
            CResourceSpec::owned_memory(CMemorySegment {
                base: c_variable("p"),
                start: if cell == 0 {
                    c_variable("start")
                } else {
                    c_int32_literal(cell)
                },
                end: c_int32_literal(cell + 1),
                element_width: 4,
                guard: None,
            })
        })
        .collect();
    vec![
        CCompositeResourceDefinition::new(
            "window",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            contains,
            vec![],
        )
        .with_instance_schema(Some(schema)),
    ]
}

fn window_instance(block: u64, identity: u64) -> CResourceFact {
    CResourceFact::own(CResource::Instance(
        ResourceInstance::new(
            Variable(identity),
            "window".into(),
            vec![CValue::pointer(heap_base(block)).into()].into(),
            ResourceFieldSchema::new(vec![("start".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap(),
            vec![int32(0).into()].into(),
        )
        .unwrap(),
    ))
}

/// The views a section's own folded field-bearing instance publishes cost
/// that instance's body: the frame the section is evaluated against may hold
/// any number of unrelated instances of the same family, each with a body
/// of its own, and none of them is evaluated.
#[test]
fn unmatched_instance_body_views_ignore_unrelated_instances() {
    let definitions = window_definitions(4);
    let mut samples = Vec::new();
    for size in SIZES {
        let frame = ResourceContext::new().unchecked_with_facts((0..size).flat_map(|index| {
            [
                owned_range(heap_base(index as u64 + 1), 0, 4),
                window_instance(index as u64 + 1, TARGET_HEAP + 1 + index as u64),
            ]
        }));
        let state = CState::new().with_resource_context(frame);
        let target = window_instance(TARGET_HEAP, 2 * TARGET_HEAP);
        let assumptions = PureFactContext::new();
        let (supply, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::resource_clause_section_supply(
                &state,
                std::slice::from_ref(&target),
                &definitions,
                &assumptions,
            )
        });
        let published = supply
            .facts()
            .iter()
            .filter(|fact| {
                matches!(fact, CResourceFact::View(CResource::Memory(range))
                    if range.base().block == PointerBlock::Heap(TARGET_HEAP))
            })
            .count();
        assert_eq!(published, 4, "the target body's four cells are published");
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("unmatched instance body views", &samples, 4.0);
}

/// The same publication grows with the instance's own body: one evaluation
/// of each owned clause, and nothing more.
#[test]
fn unmatched_instance_body_views_are_linear_in_the_body() {
    // Smaller than `SIZES`: the charged work is linear in the body, but the
    // wall time of publishing a body of 1024 owned cells is tens of seconds
    // in a debug build, which points at uncharged superlinear work somewhere
    // below this call (resource normalization of many same-block ranges is
    // the suspect) and would make this test time out under gate load. The
    // linearity claim is the same at these sizes.
    const BODY_SIZES: [usize; 4] = [4, 16, 64, 256];
    let mut samples = Vec::new();
    for size in BODY_SIZES {
        let definitions = window_definitions(size as u32);
        let state = CState::new();
        let target = window_instance(TARGET_HEAP, 2 * TARGET_HEAP);
        let assumptions = PureFactContext::new();
        let (supply, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::resource_clause_section_supply(
                &state,
                std::slice::from_ref(&target),
                &definitions,
                &assumptions,
            )
        });
        let published = supply
            .facts()
            .iter()
            .filter(|fact| matches!(fact, CResourceFact::View(CResource::Memory(_))))
            .count();
        assert_eq!(published, size, "every owned cell of the body is published");
        samples.push((size, work));
    }
    eprintln!("unmatched instance body views by body size (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    let per_clause = base_work as f64 / smallest as f64;
    for (size, work) in &samples {
        let allowed = 2.0 * per_clause * *size as f64 + 8.0;
        assert!(
            (*work as f64) <= allowed,
            "a {size}-clause body charged {work} units, above {allowed:.1} (linear in the \
             body): {samples:?}"
        );
    }
}

fn variable_range(base: Pointer, start: Bitvector32Term, end: Bitvector32Term) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new(base, start, end))
}

fn int32_equal(left: u64, right: u64) -> ConditionTerm {
    ConditionTerm::Bitvector32Equal(
        Box::new(Bitvector32Term::Variable(Variable(left))),
        Box::new(Bitvector32Term::Variable(Variable(right))),
    )
}

/// Two held ranges that abut only by a proved endpoint equality merge in
/// normalization, and finding the partner costs the endpoint's equality
/// class: unrelated equalities among other values add no work.
#[test]
fn joining_ranges_by_a_proved_endpoint_ignores_unrelated_equalities() {
    let (end, start) = (3 * TARGET_HEAP, 3 * TARGET_HEAP + 1);
    let mut samples = Vec::new();
    for size in SIZES {
        let frame = ResourceContext::new().unchecked_with_facts([
            variable_range(
                heap_base(TARGET_HEAP),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Variable(Variable(end)),
            ),
            variable_range(
                heap_base(TARGET_HEAP),
                Bitvector32Term::Variable(Variable(start)),
                Bitvector32Term::Constant(16),
            ),
        ]);
        let assumptions = (0..size as u64).fold(
            PureFactContext::new().assume_condition(int32_equal(end, start), true),
            |facts, index| {
                facts.assume_condition(
                    int32_equal(4 * TARGET_HEAP + 2 * index, 4 * TARGET_HEAP + 2 * index + 1),
                    true,
                )
            },
        );
        // The premise set's lazy indexes (the equality graph and the ones
        // any normalization consults) are built once per premise set and
        // shared by every later query. Warm them on an unrelated merge of
        // identically spelled endpoints so the measurement below is the
        // join alone.
        let warm = ResourceContext::new().unchecked_with_facts([
            variable_range(
                heap_base(TARGET_HEAP + 1),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Variable(Variable(end)),
            ),
            variable_range(
                heap_base(TARGET_HEAP + 1),
                Bitvector32Term::Variable(Variable(end)),
                Bitvector32Term::Constant(16),
            ),
        ]);
        assert_eq!(warm.normalized(&assumptions).facts().len(), 1);
        assert!(assumptions.bitvector_terms_equal_from_facts(
            &Bitvector32Term::Variable(Variable(end)),
            &Bitvector32Term::Variable(Variable(start)),
        ));
        let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame.clone().normalized(&assumptions)
        });
        assert_eq!(
            normalized.facts(),
            &[variable_range(
                heap_base(TARGET_HEAP),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(16),
            )],
            "the two ranges join into one"
        );
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("joining by a proved endpoint", &samples, 4.0);
}

/// A call that retires an allocation asks which resource the caller keeps
/// could still refer to it. Only the kept facts that can name the retired
/// block are candidates, and they come from the context's indexes, so kept
/// ranges and instances elsewhere add no work: the answer costs the block's
/// own candidates.
#[test]
fn retirement_stale_check_ignores_unrelated_kept_resources() {
    let allocation = heap_base(TARGET_HEAP);
    let bytes = Bitvector32Term::Constant(16);
    let mut samples = Vec::new();
    for size in SIZES {
        let unrelated = (0..size).flat_map(|index| {
            [
                owned_range(heap_base(index as u64 + 1), 0, 4),
                owned_instance(TARGET_HEAP + 1 + index as u64),
            ]
        });
        let kept = ResourceContext::new()
            .unchecked_with_facts(unrelated.clone())
            .unchecked_with_fact(owned_range(allocation.clone(), 4, 8));
        let assumptions = PureFactContext::new();
        let (stale, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::caller_resource_left_stale_by_retirement(
                &kept,
                &allocation,
                &bytes,
                &assumptions,
            )
            .cloned()
        });
        assert_eq!(
            stale, None,
            "a kept range past the allocation's end is separate from it"
        );
        samples.push((size, work));

        // The same frame keeping a range inside the allocation is refused,
        // so the measurement above is of a check that can say no.
        let overlapping = ResourceContext::new()
            .unchecked_with_facts(unrelated)
            .unchecked_with_fact(owned_range(allocation.clone(), 2, 3));
        assert_eq!(
            crate::kernel::functions::caller_resource_left_stale_by_retirement(
                &overlapping,
                &allocation,
                &bytes,
                &assumptions,
            ),
            Some(&owned_range(allocation.clone(), 2, 3)),
        );
    }
    assert_constant_plus_log_growth("retirement stale check", &samples, 4.0);
}
