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
    heap_base(base).offset_by_elements(MachineTerm::constant(index), 4)
}

fn range(base: u64, start: u32, end: u32) -> MemoryRange {
    MemoryRange::new(
        heap_base(base),
        MachineTerm::constant(start),
        MachineTerm::constant(end),
    )
}

/// `forall k in 0..capacity where occupied[k] == 0 { owns data[k..k + 1]; }`.
fn cells_fact(capacity: u32) -> IteratedMemory {
    IteratedMemory::new(
        "cells",
        heap_base(DATA),
        4,
        1,
        0,
        1,
        MachineTerm::constant(0),
        MachineTerm::constant(capacity),
        IteratedGuard::new(
            heap_base(OCCUPIED),
            ProgramType::Int32,
            4,
            true,
            MachineTerm::constant(0),
        ),
    )
    .expect("a one-cell element with stride one is a valid shape")
}

/// A state that owns the guard cells and holds the iterated fact, with the
/// first `free` guard cells known to be zero, the next two known to be one,
/// and the rest unknown.
fn cells_state(capacity: u32, free: u32) -> ExecutionState {
    let mut memory = Memory::new();
    for index in 0..capacity.min(free + 2) {
        memory = memory.store(cell(OCCUPIED, index), int32(u32::from(index >= free)));
    }
    ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own_memory(range(OCCUPIED, 0, capacity)))
                .unchecked_with_fact(ResourceFact::own(Resource::iterated(cells_fact(capacity)))),
        )
}

fn take(state: &ExecutionState, index: u32) -> Result<ExecutionState, String> {
    crate::kernel::apply_iterated_step(
        state,
        &crate::kernel::IteratedStep::Take {
            element: range(DATA, index, index + 1),
        },
        &PureFactContext::new(),
    )
}

fn give(state: &ExecutionState, index: u32) -> Result<ExecutionState, String> {
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
fn store_guard(state: &ExecutionState, index: u32, value: u32) -> Result<ExecutionState, String> {
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

fn held_fact(state: &ExecutionState) -> IteratedMemory {
    let facts = state.resources().iterated_facts();
    let [fact] = facts.as_slice() else {
        panic!("exactly one iterated fact should be held: {facts:?}");
    };
    let Resource::Iterated(iterated) = fact.resource() else {
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
        &ResourceFact::own_memory(range(DATA, 3, 4)),
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
        &ResourceFact::own_memory(range(DATA, 3, 4)),
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
            "{what}: size {size} charged {work} units, above {allowed:.1} \
             (constant plus {slope}·log2 growth): {samples:?}"
        );
    }
}

/// `cells(data, occupied, capacity)`: owns the guard cells and declares the
/// iterated clause over them.
fn cells_definition() -> Vec<CompositeResourceDefinition> {
    let iterated = ResourceSpec::new(
        ResourceTerm::Iterated(Box::new(crate::kernel::primitives::IteratedSpec {
            owner: "cells".into(),
            element: MemorySegment::new(
                crate::kernel::program_expression::variable("data"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::variable("capacity"),
            ),
            stride: 1,
            start_offset: 0,
            end_offset: 1,
            guard_base: crate::kernel::program_expression::variable("occupied"),
            guard_cell_type: ProgramType::Int32,
            guard_cell_width: 4,
            holds_when_equal: true,
            guard_value: crate::kernel::program_expression::int32_literal(0),
        })),
        ResourceAccessMode::Own,
        ResourceQuantity::One,
        ResourceTransferRole::Consume,
        ResourceStateSource::Current,
    )
    .unwrap();
    vec![CompositeResourceDefinition::new(
        "cells",
        vec![
            program_parameter("data", ProgramType::Int32Pointer),
            program_parameter("occupied", ProgramType::Int32Pointer),
            program_parameter("capacity", ProgramType::Int32),
        ],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("occupied"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::variable("capacity"),
            )),
            iterated,
        ],
        vec![],
    )]
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/iterated_ownership_tests.rs");
}

#[test]
fn iterated_element_selection_checks_pointer_reads_across_states() {
    let source = Pointer {
        block: "iterated-pointer-slot".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = Memory::new()
        .with_block("iterated-pointer-slot", 8)
        .store(cell(OCCUPIED, 0), int32(0));
    let after = before.clone().store(cell(UNRELATED, 0), int32(1));
    let read = |memory: &Memory, address: &Pointer| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory.clone()),
                Box::new(address.clone()),
                LoadKind::of_type(ProgramType::Int32Pointer).unwrap(),
            ),
            4,
        ),
    };
    let held_base = read(&before, &source);
    let current_base = read(&after, &source);
    assert_ne!(held_base, current_base);
    let iterated = IteratedMemory::new(
        "retained_state-cells",
        held_base,
        4,
        1,
        0,
        1,
        0u32.into(),
        1u32.into(),
        IteratedGuard::new(
            heap_base(OCCUPIED),
            ProgramType::Int32,
            4,
            true,
            0u32.into(),
        ),
    )
    .unwrap();
    let state = ExecutionState::new()
        .with_memory(after.clone())
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own_memory(range(OCCUPIED, 0, 1)))
                .unchecked_with_fact(ResourceFact::own(Resource::iterated(iterated.clone()))),
        );
    let take_at = |base| {
        crate::kernel::apply_iterated_step(
            &state,
            &crate::kernel::IteratedStep::Take {
                element: MemoryRange::new(base, 0u32.into(), 1u32.into()),
            },
            &PureFactContext::new(),
        )
    };
    let mut equivalent = iterated.clone();
    equivalent.element_base = current_base.clone();
    assert!(crate::kernel::primitives::iterated_memories_proven_equal(
        &iterated,
        &equivalent,
        &PureFactContext::new(),
    ));
    assert!(
        state
            .resources()
            .clone()
            .without_fact_incrementally(
                &ResourceFact::own(Resource::iterated(equivalent.clone())),
                &PureFactContext::new(),
            )
            .is_some()
    );
    equivalent.element_width = 8;
    assert!(!crate::kernel::primitives::iterated_memories_proven_equal(
        &iterated,
        &equivalent,
        &PureFactContext::new(),
    ));
    equivalent = iterated.clone();
    equivalent.guard.base = equivalent.guard.base.offset_by_bytes(4);
    assert!(!crate::kernel::primitives::iterated_memories_proven_equal(
        &iterated,
        &equivalent,
        &PureFactContext::new(),
    ));
    let held_element = iterated.element_range(&0u32.into());
    let taken = crate::kernel::apply_iterated_step(
        &state,
        &crate::kernel::IteratedStep::Take {
            element: held_element.clone(),
        },
        &PureFactContext::new(),
    )
    .unwrap();
    let extra = ResourceFact::own_memory(MemoryRange::new(
        iterated.element_base.clone(),
        1u32.into(),
        2u32.into(),
    ));
    let taken_resources = taken
        .resources()
        .clone()
        .try_compose_with_facts([extra], &PureFactContext::new())
        .unwrap();
    let taken = taken.with_resource_context(taken_resources);
    let give = crate::kernel::IteratedStep::Give {
        element: MemoryRange::new(current_base.clone(), 0u32.into(), 1u32.into()),
    };
    let returned = crate::kernel::apply_iterated_step(&taken, &give, &PureFactContext::new())
        .expect("giving the same pointer read back must consume the held element");
    assert!(
        returned
            .resources()
            .clone()
            .without_fact_incrementally(
                &ResourceFact::own(Resource::iterated(iterated.clone())),
                &PureFactContext::new(),
            )
            .is_some()
    );
    assert!(
        returned
            .resources()
            .clone()
            .without_fact_incrementally(
                &ResourceFact::own_memory(held_element),
                &PureFactContext::new(),
            )
            .is_none(),
        "giving must not leave a second copy of the element"
    );
    assert!(crate::kernel::apply_iterated_step(&returned, &give, &PureFactContext::new()).is_err());
    assert!(
        take_at(current_base).is_ok(),
        "an unrelated store preserves the selected pointer read"
    );
    assert!(
        take_at(read(&after, &source.offset_by_bytes(8))).is_err(),
        "a different read address is not the held base"
    );
    let changed = after.clone().store(
        source.clone(),
        ProgramValue::typed_pointer(heap_base(DATA + 100), ProgramType::Int32Pointer),
    );
    assert!(
        take_at(read(&changed, &source)).is_err(),
        "a changed pointer slot is not the original read"
    );
}
