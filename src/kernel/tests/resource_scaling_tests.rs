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
