//! Iterated guarded ownership: the checked element steps, the store rule,
//! and deterministic scaling regressions for each.
//!
//! The fact is one resource for a whole index range and must never be
//! enumerated, so every operation here is measured at four range sizes: an
//! operation on one index, and a separation query, must cost the same
//! whatever the range holds; a loop over `M` indices must cost linear work in
//! `M`; and folding or unfolding the resource that declares the clause must
//! not depend on the range at all.

use super::*;

const SIZES: [u32; 4] = [64, 256, 1024, 4096];

/// Loop lengths for the linear-in-`M` regression. Each claimed element is one
/// C store, so the memory history grows with `M`; these stay within the
/// default test-thread stack.
const LOOP_SIZES: [u32; 4] = [32, 64, 128, 256];

const DATA: u64 = 7_000_001;
const OCCUPIED: u64 = 7_000_002;
const UNRELATED: u64 = 7_000_003;

fn heap_base(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::Heap(identity),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn cell(base: u64, index: u32) -> Pointer {
    heap_base(base).offset_by_elements(Bitvector32Term::Constant(index), 4)
}

fn range(base: u64, start: u32, end: u32) -> CMemoryRange {
    CMemoryRange::new(
        heap_base(base),
        Bitvector32Term::Constant(start),
        Bitvector32Term::Constant(end),
    )
}

/// `forall k in 0..capacity where occupied[k] == 0 { owns data[k..k + 1]; }`.
fn cells_fact(capacity: u32) -> CIteratedMemory {
    CIteratedMemory::new(
        "cells",
        heap_base(DATA),
        4,
        1,
        0,
        1,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(capacity),
        CIteratedGuard::new(
            heap_base(OCCUPIED),
            CType::Int32,
            4,
            true,
            Bitvector32Term::Constant(0),
        ),
    )
    .expect("a one-cell element with stride one is a valid shape")
}

/// A state that owns the guard cells and holds the iterated fact, with the
/// first `free` guard cells known to be zero, the next two known to be one,
/// and the rest unknown.
fn cells_state(capacity: u32, free: u32) -> CState {
    let mut memory = CMemory::new();
    for index in 0..capacity.min(free + 2) {
        memory = memory.store(cell(OCCUPIED, index), int32(u32::from(index >= free)));
    }
    CState::new().with_memory(memory).with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(range(OCCUPIED, 0, capacity)))
            .unchecked_with_fact(CResourceFact::own(CResource::iterated(cells_fact(
                capacity,
            )))),
    )
}

fn take(state: &CState, index: u32) -> Result<CState, String> {
    crate::kernel::apply_iterated_step(
        state,
        &crate::kernel::IteratedStep::Take {
            element: range(DATA, index, index + 1),
        },
        &PureFactContext::new(),
    )
}

fn give(state: &CState, index: u32) -> Result<CState, String> {
    crate::kernel::apply_iterated_step(
        state,
        &crate::kernel::IteratedStep::Give {
            element: range(DATA, index, index + 1),
        },
        &PureFactContext::new(),
    )
}

/// One C store of `value` to the guard cell at `index`, through the store
/// rule exactly as the statement evaluator applies it.
fn store_guard(state: &CState, index: u32, value: u32) -> Result<CState, String> {
    let pointer = cell(OCCUPIED, index);
    let value = int32(value);
    let assumptions = PureFactContext::new();
    let plan = crate::kernel::plan_iterated_guard_store(state, &pointer, &value, &assumptions)?;
    let mut next = state
        .clone()
        .with_resource_context(plan.before_store(state.resources().clone())?);
    let memory = next.memory().clone().store(pointer, value);
    next.set_memory_with_checked_stores(memory, true);
    let resources = plan.after_store(next.resources().clone())?;
    Ok(next.with_resource_context(resources))
}

fn held_fact(state: &CState) -> CIteratedMemory {
    let facts = state.resources().iterated_facts();
    let [fact] = facts.as_slice() else {
        panic!("exactly one iterated fact should be held: {facts:?}");
    };
    let CResource::Iterated(iterated) = fact.resource() else {
        unreachable!()
    };
    iterated.as_ref().clone()
}

#[test]
fn allocation_and_release_protocols_keep_the_fact_exact() {
    let capacity = 16;
    let state = cells_state(capacity, 8);
    // Allocation: take the free cell, then mark it. The mark closes the hole.
    let taken = take(&state, 3).expect("a free cell can be taken");
    assert_eq!(held_fact(&taken).holes().len(), 1);
    assert!(taken.resources().satisfies_fact(
        &CResourceFact::own_memory(range(DATA, 3, 4)),
        &PureFactContext::new()
    ));
    let marked = store_guard(&taken, 3, 1).expect("the taken cell's guard may be written");
    assert!(held_fact(&marked).holes().is_empty());
    assert_eq!(held_fact(&marked), cells_fact(capacity));
    // Release: clearing the mark while the element is owned opens a hole,
    // and giving the element back closes it.
    let cleared = store_guard(&marked, 3, 0).expect("an element owned outright may be released");
    assert_eq!(held_fact(&cleared).holes().len(), 1);
    let given = give(&cleared, 3).expect("the released element goes back");
    assert!(held_fact(&given).holes().is_empty());
    assert!(!given.resources().satisfies_fact(
        &CResourceFact::own_memory(range(DATA, 3, 4)),
        &PureFactContext::new()
    ));
}

#[test]
fn element_steps_and_guard_stores_refuse_what_the_fact_may_hold() {
    let state = cells_state(16, 8);
    // Cell 9 is occupied: nothing to take, and nothing to give back.
    assert!(take(&state, 9).unwrap_err().contains("guard is false"));
    // The guard of cell 12 is not known at all.
    assert!(take(&state, 12).unwrap_err().contains("not known to hold"));
    // Out of range.
    assert!(take(&state, 20).is_err());
    // Cell 2 is free and held: marking it without taking it out would
    // silently drop the cell from the fact.
    assert!(
        store_guard(&state, 2, 1)
            .unwrap_err()
            .contains("the guard holds at this index")
    );
    // Taking the same element twice is refused while the first is out.
    let taken = take(&state, 2).unwrap();
    assert!(
        take(&taken, 2)
            .unwrap_err()
            .contains("already be taken out")
    );
    // Giving back an element whose guard is false is refused.
    let marked = store_guard(&taken, 2, 1).unwrap();
    assert!(give(&marked, 2).unwrap_err().contains("guard is false"));
}

#[test]
fn a_store_that_escapes_the_store_rule_drops_the_fact() {
    let state = cells_state(16, 8);
    // An unchecked store to a guard cell the fact still claims.
    let mut next = state.clone();
    let memory = next.memory().clone().store(cell(OCCUPIED, 2), int32(1));
    next.set_memory(memory);
    assert!(next.resources().iterated_facts().is_empty());
    // An unchecked store to an unrelated block keeps it.
    let mut next = state.clone();
    let memory = next.memory().clone().store(cell(UNRELATED, 0), int32(1));
    next.set_memory(memory);
    assert_eq!(next.resources().iterated_facts().len(), 1);
}

fn log2(size: u32) -> f64 {
    f64::from(size).log2()
}

fn assert_constant_plus_log(what: &str, samples: &[(u32, usize)], slope: f64) {
    eprintln!("{what} (N, units): {samples:?}");
    let (smallest, base) = samples[0];
    for (size, work) in samples {
        let allowed = base as f64 + slope * (log2(*size) - log2(smallest));
        assert!(
            (*work as f64) <= allowed,
            "{what}: a range of {size} cells charged {work} units, above {allowed:.1} \
             (constant plus {slope}·log2 growth): {samples:?}"
        );
    }
}

#[test]
fn taking_one_element_is_constant_in_the_range_size() {
    let mut samples = Vec::new();
    for size in SIZES {
        let state = cells_state(size, size);
        let (taken, work) =
            crate::instrumentation::measure_deterministic_work(|| take(&state, size / 2));
        taken.expect("the middle cell is free");
        samples.push((size, work));
    }
    assert_constant_plus_log("taking one element", &samples, 4.0);
}

#[test]
fn a_loop_taking_m_elements_is_linear_in_m() {
    let capacity = 8192;
    let mut samples = Vec::new();
    for claimed in LOOP_SIZES {
        let state = cells_state(capacity, claimed);
        let (claimed_state, work) = crate::instrumentation::measure_deterministic_work(|| {
            (0..claimed).try_fold(state.clone(), |state, index| {
                store_guard(&take(&state, index)?, index, 1)
            })
        });
        let claimed_state = claimed_state.expect("every free cell can be claimed");
        assert!(held_fact(&claimed_state).holes().is_empty());
        samples.push((claimed, work));
    }
    eprintln!("claiming M elements (M, units): {samples:?}");
    for window in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = window else {
            unreachable!()
        };
        // Twice the elements may cost at most two and a half times the
        // work: a quadratic loop would cost four.
        let ratio = *large_work as f64 / *small_work as f64;
        let elements = f64::from(*large) / f64::from(*small);
        assert!(
            ratio <= elements * 1.25,
            "claiming {large} elements charged {large_work} units against {small_work} for \
             {small}: growth {ratio:.2} for {elements}x the elements ({samples:?})"
        );
    }
}

#[test]
fn separation_from_an_unrelated_range_is_constant_in_the_range_size() {
    let mut samples = Vec::new();
    for size in SIZES {
        let fact = CResource::iterated(cells_fact(size));
        let unrelated = CResource::Memory(range(UNRELATED, 0, 4));
        let assumptions = PureFactContext::new();
        let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.proves_resource_separate(&fact, &unrelated)
        });
        assert!(separate, "a range in another block is separate");
        samples.push((size, work));
    }
    assert_constant_plus_log("separation from an unrelated range", &samples, 2.0);
    // A range that may hold an element is never proved separate.
    let fact = CResource::iterated(cells_fact(16));
    assert!(
        !PureFactContext::new()
            .proves_resource_separate(&fact, &CResource::Memory(range(DATA, 3, 4)))
    );
}

/// `cells(data, occupied, capacity)`: owns the guard cells and declares the
/// iterated clause over them.
fn cells_definition() -> Vec<CCompositeResourceDefinition> {
    let iterated = CResourceSpec::new(
        CResourceTerm::Iterated(Box::new(crate::kernel::primitives::CIteratedSpec {
            owner: "cells".into(),
            element: CMemorySegment::new(
                c_variable("data"),
                c_int32_literal(0),
                c_variable("capacity"),
            ),
            stride: 1,
            start_offset: 0,
            end_offset: 1,
            guard_base: c_variable("occupied"),
            guard_cell_type: CType::Int32,
            guard_cell_width: 4,
            holds_when_equal: true,
            guard_value: c_int32_literal(0),
        })),
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    vec![CCompositeResourceDefinition::new(
        "cells",
        vec![
            c_parameter("data", CType::Int32Pointer),
            c_parameter("occupied", CType::Int32Pointer),
            c_parameter("capacity", CType::Int32),
        ],
        None,
        false,
        vec![
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("occupied"),
                c_int32_literal(0),
                c_variable("capacity"),
            )),
            iterated,
        ],
        vec![],
    )]
}

#[test]
fn unfolding_the_declaring_resource_is_constant_in_the_range_size() {
    let definitions = cells_definition();
    let mut samples = Vec::new();
    for size in SIZES {
        let folded = CResourceFact::own(CResource::Composite {
            name: "cells".into(),
            arguments: vec![
                CValue::pointer(heap_base(DATA)).into(),
                CValue::pointer(heap_base(OCCUPIED)).into(),
                int32(size).into(),
            ]
            .into(),
        });
        let context = ResourceContext::new().unchecked_with_fact(folded.clone());
        let memory = CMemory::new();
        let assumptions = PureFactContext::new();
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::functions::expand_composite_resource_fact(
                &context,
                &folded,
                &definitions,
                &memory,
                &assumptions,
            )
        });
        let expanded = expanded.expect("the body expands");
        assert!(
            expanded.contains_exact_representation(&CResourceFact::own(CResource::iterated(
                cells_fact(size)
            )))
        );
        // Folding is the same exchange read backwards: the folded head is
        // what remains once the exposed body is consumed.
        let folded_again = expanded
            .clone()
            .without_fact(
                &CResourceFact::own(CResource::iterated(cells_fact(size))),
                &assumptions,
            )
            .and_then(|context| {
                context.without_fact(
                    &CResourceFact::own_memory(range(OCCUPIED, 0, size)),
                    &assumptions,
                )
            })
            .expect("the exposed body can be consumed");
        assert!(folded_again.is_empty());
        samples.push((size, work));
    }
    assert_constant_plus_log("unfolding the declaring resource", &samples, 4.0);
}
