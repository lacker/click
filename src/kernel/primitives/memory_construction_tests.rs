use super::*;

fn assert_explained(memory: &Memory) {
    let mut pending = vec![memory.clone()];
    let mut seen = std::collections::HashSet::new();
    while let Some(memory) = pending.pop() {
        if !seen.insert(memory.diagnostic_identity()) {
            continue;
        }
        match memory.diagnostic_construction() {
            Some(MemoryConstructionKind::Transition(edge)) => {
                pending.push(edge.base().memory().clone());
                if let MemoryDerivation::CellsSeeded { run, .. } = edge.as_ref() {
                    pending.push(run.source().memory().clone());
                }
            }
            Some(MemoryConstructionKind::Transform { sources, .. }) => {
                assert!(!sources.is_empty());
                pending.extend(sources.iter().cloned());
            }
            None => assert!(memory.is_initial_diagnostic_memory(), "unexplained memory"),
        }
        assert!(seen.len() < 100, "unexpected construction cycle");
    }
}

#[test]
fn memory_constructions_cover_non_transition_producers() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: "local:construction".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new()
        .with_block("local:construction", 16)
        .store(pointer.clone(), ProgramValue::Int32(7.into()));
    let projected = crate::kernel::memory_provenance::canonical_program_memory_for_pointer_load(
        &memory,
        &Pointer::symbolic(Variable(990_810)),
    );
    assert!(matches!(
        projected.diagnostic_construction(),
        Some(MemoryConstructionKind::Transform {
            operation: "project memory for pointer read",
            ..
        })
    ));
    let variants = [
        projected,
        crate::kernel::memory_provenance::canonical_memory_deep(&memory),
        memory.without_cell(&pointer),
        memory.clone().with_uninitialized_object(pointer.clone(), 4),
        memory.clone().with_block_without_derivation("synthetic", 4),
        memory.clone().with_block("havoc:990811", 0),
        memory.clone().store_union(
            pointer.clone(),
            ProgramType::Int32,
            ProgramValue::Int32(8.into()),
        ),
        crate::kernel::reasoning::substitute_pointer_variable_in_memory(
            &memory,
            Variable(990_810),
            &pointer,
        ),
        memory
            .clone()
            .with_interface_memory_havoc_preserving_loans(
                Variable(990_812),
                &BTreeSet::new(),
                &[&memory],
                None,
            )
            .unwrap(),
    ];
    for memory in variants {
        assert_explained(&memory);
    }
}

#[test]
fn construction_metadata_does_not_change_memory_identity_or_proof_edges() {
    let _session = crate::kernel::VerificationSession::enter();
    let original = Memory::new().with_block("local:identity", 4);
    let interned = intern_memory_ref(&original);
    let mut described = original.clone();
    // A distinct diagnostic path describes exactly the same semantic state.
    described.record_diagnostic_transform("diagnostic test", vec![Memory::new()], Vec::new());
    assert_eq!(original, described);
    assert_eq!(
        memory_content_hash(&original),
        memory_content_hash(&described)
    );
    assert_eq!(interned, intern_memory_ref(&described));
    assert_eq!(
        interned.read_identity(),
        intern_memory_ref(&described).read_identity()
    );
    assert_eq!(interned.derivation().unwrap().kind_name(), "BlockDeclared");
}

#[test]
fn unrecorded_mutation_cannot_inherit_an_incorrect_origin() {
    let original = Memory::new().with_block("local:changed", 4);
    let mut changed = original.clone();
    Arc::make_mut(&mut changed.blocks).insert("local:extra".into(), MemoryBlock::new(4));
    assert!(changed.diagnostic_construction().is_none());
    assert!(original.diagnostic_construction().is_some());
}

#[test]
fn construction_pins_detect_mutation_of_an_uninterned_state() {
    let pointer = Pointer {
        block: "local:unpinned".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut memory = Memory::new().with_uninitialized_object(pointer.clone(), 4);
    assert!(memory.diagnostic_construction().is_some());
    Arc::make_mut(&mut memory.heap)
        .uninitialized_objects
        .insert(pointer, 8);
    assert!(memory.diagnostic_construction().is_none());
}

/// A loop back edge may add the tombstone of an allocation the head never
/// held as live, and nothing else: a tombstone for storage the head held
/// live, or any change to the live set, still differs.
#[test]
fn allocation_lifetimes_up_to_ended_admit_only_new_tombstones() {
    let _session = crate::kernel::VerificationSession::enter();
    let freed = Pointer::symbolic(Variable(990_901));
    let live = Pointer::symbolic(Variable(990_902));
    let size = MachineTerm::constant(8);
    let mut head = HeapMemory::default();
    head.live_allocations
        .insert(live.clone(), HeapExtent::int32(size.clone()));

    let mut ended_elsewhere = head.clone();
    ended_elsewhere
        .deallocated_allocations
        .insert(freed.clone(), HeapExtent::int32(size.clone()));
    assert!(head.has_same_allocation_lifetimes_up_to_ended(&ended_elsewhere));
    assert!(!head.have_same_allocation_lifetimes(&ended_elsewhere));
    // The relation is not symmetric: a back edge cannot drop a tombstone
    // the head recorded.
    assert!(!ended_elsewhere.has_same_allocation_lifetimes_up_to_ended(&head));

    let mut ended_live = head.clone();
    ended_live.live_allocations.remove(&live);
    ended_live
        .deallocated_allocations
        .insert(live.clone(), HeapExtent::int32(size.clone()));
    assert!(!head.has_same_allocation_lifetimes_up_to_ended(&ended_live));

    let mut tombstone_for_live = head.clone();
    tombstone_for_live
        .deallocated_allocations
        .insert(live.clone(), HeapExtent::int32(size.clone()));
    assert!(!head.has_same_allocation_lifetimes_up_to_ended(&tombstone_for_live));

    let mut allocated = head.clone();
    allocated
        .live_allocations
        .insert(freed, HeapExtent::int32(size));
    assert!(!head.has_same_allocation_lifetimes_up_to_ended(&allocated));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/primitives/memory_construction_tests.rs");
}
