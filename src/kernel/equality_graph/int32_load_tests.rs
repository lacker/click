use super::*;
use crate::kernel::MachineCastSpelling;
use crate::kernel::binary_node;
fn var(id: u64) -> MachineTerm {
    MachineTerm::Variable(Variable(id))
}
fn address(id: u64) -> Pointer {
    Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::scale_int32(var(id), 4),
    }
}
fn load(memory: &SharedMemory, pointer: &Pointer, bytes: u32) -> MachineTerm {
    MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
        memory,
        pointer,
        crate::kernel::LoadKind::Int32,
        bytes,
    ))
}
fn memory() -> SharedMemory {
    intern_memory(Memory::new().with_block("array", 4096))
}

#[test]
fn int32_load_congruence_handles_early_and_late_offsets_and_scalar_parents() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let (left, right) = (load(&memory, &address(1), 4), load(&memory, &address(2), 4));
    let add = |v| binary_node!(Int32, Add, Box::new(v), Box::new(var(3)));
    for early in [false, true] {
        let mut graph = EqualityGraph::default();
        if early {
            graph.add_int32_equality(&var(1), &var(2));
        }
        graph.add_int32_equality(&add(left.clone()), &var(10));
        graph.add_int32_equality(&add(right.clone()), &var(11));
        if !early {
            assert!(!graph.are_int32_equal(&var(10), &var(11)));
            graph.add_int32_equality(&var(2), &var(1));
        }
        assert!(graph.are_int32_equal(&var(10), &var(11)));
    }
}

#[test]
fn shallow_scalar_decision_uses_only_registered_loads_in_one_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let left = load(&before, &address(1), 4);
    let right = load(&before, &address(2), 4);
    let after = intern_memory(
        before
            .memory()
            .clone()
            .store(address(1), ProgramValue::Int32(MachineTerm::constant(9))),
    );
    let changed = load(&after, &address(2), 4);
    let context =
        PureFactContext::new().assume_condition(ConditionTerm::equal(var(1), var(2)), true);
    assert_eq!(
        context.decide_bitvector_equality_shallow(&left, &right),
        Some(true)
    );
    assert_eq!(
        context.decide(&ConditionTerm::equal(left.clone(), right.clone())),
        Some(true)
    );
    assert_ne!(
        context.decide_bitvector_equality_shallow(&left, &changed),
        Some(true)
    );
    assert_ne!(
        context.decide(&ConditionTerm::equal(left, changed)),
        Some(true)
    );
}

#[test]
fn int32_load_congruence_keeps_states_blocks_and_widths_distinct() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let left = load(&memory, &address(1), 4);
    let right = load(&memory, &address(2), 4);
    let after = intern_memory(
        memory
            .memory()
            .clone()
            .store(address(1), ProgramValue::Int32(MachineTerm::constant(9))),
    );
    let changed = load(&after, &address(2), 4);
    let mut other_block = address(2);
    other_block.block = "other".into();
    let other = load(&memory, &other_block, 4);
    let narrow = load(&memory, &address(3), 2);
    let wide = load(&memory, &address(4), 8);
    let mut graph = EqualityGraph::default();
    for i in 2..=4 {
        graph.add_int32_equality(&var(1), &var(i));
    }
    assert!(graph.are_int32_equal(&left, &right));
    for unknown in [changed, other, narrow, wide] {
        assert!(!graph.are_int32_equal(&left, &unknown));
    }
    assert!(!graph.are_int32_equal(&left, &MachineTerm::constant(9)));
}

#[test]
fn int32_load_congruence_is_branch_local() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let left = load(&memory, &address(1), 4);
    let right = load(&memory, &address(2), 4);
    let equality = ConditionTerm::equal(var(1), var(2));
    let parent = PureFactContext::new();
    assert!(!parent.equality_graph.are_int32_equal(&left, &right));
    let sibling = parent.clone();
    let context = parent.clone().assume_condition(equality.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&left, &right));
    assert!(!parent.equality_graph.are_int32_equal(&left, &right));
    assert!(!sibling.equality_graph.are_int32_equal(&left, &right));
    assert!(
        !context
            .restricted_to_facts(&[], &[])
            .equality_graph
            .are_int32_equal(&left, &right)
    );
}

#[test]
fn int32_load_defining_state_is_independent_of_live_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let after = intern_memory(
        before
            .memory()
            .clone()
            .store(address(1), ProgramValue::Int32(MachineTerm::constant(9))),
    );
    let left = MachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
        &before,
        &address(1),
        crate::kernel::LoadKind::Int32,
        4,
        &before,
    ));
    crate::kernel::eval::begin_load_origin_epoch();
    // Change the mutable origin while retaining the exact defining state.
    let renamed = MachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
        &before,
        &address(1),
        crate::kernel::LoadKind::Int32,
        4,
        &after,
    ));
    assert_eq!(left, renamed);
    let right = load(&after, &address(2), 4);
    for term in [&left, &right] {
        let MachineTerm::Variable(variable) = term else {
            panic!("registered load")
        };
        assert_eq!(
            crate::kernel::eval::registered_load_origin_for_variable(variable)
                .unwrap()
                .0
                .arena_id(),
            after.arena_id()
        );
    }
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&var(1), &var(2));
    assert!(!graph.are_int32_equal(&left, &right));
    let raw = |m: &SharedMemory| {
        MachineTerm::MemoryLoad(
            m.clone(),
            Box::new(address(1)),
            crate::kernel::LoadKind::Int32,
        )
    };
    crate::kernel::eval::declare_load_access_width(&address(1), 4);
    assert!(!graph.are_int32_equal(&raw(&before), &raw(&after)));
}

#[test]
fn int32_load_registration_can_follow_a_later_width_declaration() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let left = load(&memory, &address(1), 2);
    let right = load(&memory, &address(2), 4);
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&var(1), &var(2));
    assert!(!graph.are_int32_equal(&left, &right));
    assert_eq!(left, load(&memory, &address(1), 4));
    assert!(graph.are_int32_equal(&left, &right));
}

#[test]
fn explicit_cross_state_load_equality_composes_without_merging_states() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let after = intern_memory(
        before
            .memory()
            .clone()
            .store(address(3), ProgramValue::Int32(MachineTerm::constant(9))),
    );
    let old_i = load(&before, &address(1), 4);
    let new_i = load(&after, &address(1), 4);
    let old_j = load(&before, &address(2), 4);
    let new_j = load(&after, &address(2), 4);
    // This edge represents a separately checked transport conclusion. The
    // graph must compose it, but must not itself infer that a store is disjoint.
    let bridge = ConditionTerm::equal(old_i.clone(), new_i.clone());
    let indices = ConditionTerm::equal(var(1), var(2));
    let parent = PureFactContext::new().assume_condition(indices.clone(), true);
    assert!(parent.equality_graph.are_int32_equal(&old_i, &old_j));
    assert!(!parent.equality_graph.are_int32_equal(&old_j, &new_j));
    let sibling = parent.clone();
    let context = parent.clone().assume_condition(bridge.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&old_j, &new_j));
    assert!(!sibling.equality_graph.are_int32_equal(&old_j, &new_j));
    assert!(!context.equality_graph.are_int32_equal(
        &load(&before, &address(3), 4),
        &load(&after, &address(3), 4)
    ));
    let restricted = context.restricted_to_facts(&[(bridge.clone(), true)], &[]);
    assert!(restricted.equality_graph.are_int32_equal(&old_i, &new_i));
    assert!(!restricted.equality_graph.are_int32_equal(&old_j, &new_j));
    let reverse_order = PureFactContext::new()
        .assume_condition(bridge, true)
        .assume_condition(indices, true);
    assert!(reverse_order.equality_graph.are_int32_equal(&old_j, &new_j));
}

#[test]
fn reads_at_equal_addresses_are_equal_without_equal_pointers() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_memory(Memory::new().with_block("left", 64).with_block("right", 64));
    let at = |block: &str, bytes: i64| Pointer {
        block: block.into(),
        offset: PointerOffsetTerm::Constant(bytes),
    };
    let address_of = |pointer: Pointer| MachineTerm::pointer_address(pointer);
    let after = intern_memory(
        memory
            .memory()
            .clone()
            .store(at("left", 8), ProgramValue::Int32(MachineTerm::constant(9))),
    );
    for field in [0, 8] {
        let left = load(&memory, &at("left", field), 4);
        let right = load(&memory, &at("right", field), 4);
        let changed = load(&after, &at("right", field), 4);
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_int32_equal(&left, &right));
        graph.add_uint64_equality(&address_of(at("left", 0)), &address_of(at("right", 0)));
        assert!(graph.are_int32_equal(&left, &right), "field at {field}");
        assert!(!graph.are_int32_equal(&left, &changed));
        assert!(!graph.are_equal(&at("left", field), &at("right", field)));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/int32_load_tests.rs");
}

#[test]
fn native_pointer_aliases_reach_named_nested_pointer_reads() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let field = address(940_061);
    let arena = Pointer::symbolic(Variable(940_062));
    let native = Pointer::loaded_value(&memory, &field);
    let mut graph = EqualityGraph::default();
    graph.add_equality(&native, &arena);
    let named_read = |address: &Pointer| {
        let value = Pointer::loaded(&load(&memory, address, 8)).unwrap();
        graph.register_pointer_read_definition(&value, &memory, address);
        value
    };
    let named_arena = named_read(&field);
    let direct = named_read(&arena.clone().offset_by_bytes(8));
    let indirect = named_read(&named_arena.offset_by_bytes(8));
    let direct_cell = direct.clone().offset_by_elements(var(940_063), 4);
    let indirect_cell = indirect.clone().offset_by_elements(var(940_063), 4);
    let scalar_left = load(&memory, &direct_cell, 4);
    let scalar_right = load(&memory, &indirect_cell, 4);
    assert!(graph.are_int32_equal(&scalar_left, &scalar_right));
    let other_cell = indirect.clone().offset_by_elements(var(940_064), 4);
    assert!(!graph.are_int32_equal(&scalar_left, &load(&memory, &other_cell, 4)));
    let other_width = indirect.clone().offset_by_elements(var(940_063), 8);
    assert!(!graph.are_int32_equal(&scalar_left, &load(&memory, &other_width, 4)));
    let unrelated = EqualityGraph::default();
    assert!(!unrelated.are_int32_equal(&scalar_left, &scalar_right));
    assert!(graph.are_equal(&direct, &indirect));
    // The pointee width does not enter a read's identity: the same read
    // with another stride names the same pointer, and its displacement
    // still distinguishes it.
    let other_stride = Pointer::loaded(&load(&memory, &field, 8)).unwrap();
    assert_eq!(other_stride, named_arena);
    assert!(graph.are_equal(&other_stride, &arena));
    assert!(!graph.are_equal(&other_stride.offset_by_bytes(8), &arena));
    // A scalar-indexed address beside the same load is not the read.
    let scalar_indexed = field
        .clone()
        .offset_by_elements(load(&memory, &field, 8), 8);
    assert!(scalar_indexed.as_loaded_value().is_none());
    assert!(!graph.are_equal(&scalar_indexed, &arena));
}

#[test]
fn int32_load_congruence_connects_base_reads_to_early_and_late_zero_offsets() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let base = address(940_081);
    let offset = var(940_082);
    let direct = load(&memory, &base, 4);
    let indexed = load(&memory, &base.offset_by_elements(offset.clone(), 4), 4);
    for early in [false, true] {
        let mut graph = EqualityGraph::default();
        if early {
            graph.add_int32_equality(&offset, &MachineTerm::constant(0));
        }
        graph.add_int32_equality(&direct, &var(940_083));
        graph.add_int32_equality(&indexed, &var(940_084));
        if !early {
            assert!(!graph.are_int32_equal(&var(940_083), &var(940_084)));
            graph.add_int32_equality(&offset, &MachineTerm::constant(0));
        }
        assert!(
            graph.are_int32_equal(&var(940_083), &var(940_084)),
            "early={early}"
        );
    }
}

#[test]
fn a_late_zero_index_alias_transfers_an_admitted_read_order() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let base = address(940_085);
    let index = var(940_086);
    let direct = load(&memory, &base, 4);
    let indexed = load(&memory, &base.offset_by_elements(index.clone(), 4), 4);
    let next = load(
        &memory,
        &base.offset_by_elements(MachineTerm::add(index.clone(), 1u32.into()), 4),
        4,
    );
    let known = ConditionTerm::signed_less_than(next.clone(), indexed);
    let target = ConditionTerm::signed_less_than(next, direct);
    let root = PureFactContext::new().assume_condition(known, true);
    assert_eq!(root.decide(&target), None);
    let zero = Proposition::ConditionIs(ConditionTerm::equal(index, 0u32.into()), true);
    let equal = root.assume_proposition(zero.clone());
    assert_eq!(equal.decide(&target), Some(true));
    assert_eq!(
        crate::kernel::reasoning::decide_with_facts(&equal, &ExecutionFacts::new(), &target),
        Some(true),
    );
}

/// R-mem: each 32-bit read is its own load, and the two reads of one cell
/// at the two signednesses are related by σ, a node of its own: the
/// `uint32` read is σ of the `int32` read, and reads of two cells stay
/// distinct until their addresses are. Relating them is the same work
/// whatever else the graph holds.
#[test]
fn reads_of_one_cell_at_both_signednesses_are_related() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let read = |pointer: &Pointer, kind| {
        MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &memory, pointer, kind, 4,
        ))
    };
    let signed = read(&address(1), crate::kernel::LoadKind::Int32);
    let unsigned = read(&address(1), crate::kernel::LoadKind::UInt32);
    let other = read(&address(2), crate::kernel::LoadKind::UInt32);
    let sigma = |value| {
        MachineTerm::sign_cast32(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::MachineIntegerType::UInt32,
            value,
        )
    };
    assert_ne!(signed, unsigned, "each read is its own load");
    let cold_reads = crate::kernel::eval::capture_load_variable_registry();
    let mut samples = Vec::new();
    for unrelated in [4_u64, 64, 512] {
        crate::kernel::eval::restore_load_variable_registry(&cold_reads);
        // Keep term-bridge imports and canonical forms cold at every sample
        // size.
        crate::kernel::clear_integer_bridge_memo();
        crate::kernel::eval::clear_load_canonicalization_caches();
        crate::kernel::memory_provenance::clear_canonical_form_caches();
        let mut graph = EqualityGraph::default();
        for index in 0..unrelated {
            graph.add_int32_equality(&var(500 + index), &var(5_000 + index));
        }
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.are_int32_equal(&sigma(signed.clone()), &unsigned)
        });
        assert!(equal, "R-mem relates the two reads of one cell by σ");
        assert!(
            !graph.are_int32_equal(&unsigned, &signed),
            "σ is a node of its own"
        );
        assert!(!graph.are_int32_equal(&unsigned, &other));
        graph.add_int32_equality(&var(1), &var(2));
        assert!(graph.are_int32_equal(&sigma(signed.clone()), &other));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

/// Rule K8 as a relation: a sum of the `int32` widenings of `n` narrow
/// loads is interned with constant work per widening, and is σ of the
/// `uint32` sum of the loads' `uint32` widenings (R-dist and R-comp), at
/// every size.
#[test]
fn widening_chains_are_related_with_constant_work_per_widening() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let read = |index: u64| {
        MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &address(10_000 + index),
            crate::kernel::LoadKind::UInt8,
            1,
        ))
    };
    let widen = |value: MachineTerm| MachineTerm::Cast {
        spelling: MachineCastSpelling::Generic,
        value: Box::new(value),
        from: MachineIntegerType::UInt8,
        to: MachineIntegerType::Int32,
    };
    let sizes = [8_u64, 32, 128, 512];
    let cold_reads = crate::kernel::eval::capture_load_variable_registry();
    let mut samples = Vec::new();
    for size in sizes {
        crate::kernel::eval::restore_load_variable_registry(&cold_reads);
        // Keep descriptor caches and term-bridge imports cold at every sample size.
        crate::kernel::clear_integer_bridge_memo();
        let word = |value: MachineTerm| MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: Box::new(value),
            from: MachineIntegerType::UInt8,
            to: MachineIntegerType::UInt32,
        };
        let mut widened = widen(read(0));
        let mut words = word(read(0));
        for index in 1..size {
            widened = binary_node!(Int32, Add, Box::new(widened), Box::new(widen(read(index))));
            words = binary_node!(UInt32, Add, Box::new(words), Box::new(word(read(index))));
        }
        let words =
            MachineTerm::sign_cast32(MachineIntegerType::UInt32, MachineIntegerType::Int32, words);
        let mut graph = EqualityGraph::default();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_int32_equality(&widened, &var(900_000 + size));
        });
        assert!(
            graph.are_int32_equal(&var(900_000 + size), &words),
            "size {size}"
        );
        samples.push(work);
    }
    let per_widening =
        |i: usize| (samples[i + 1] - samples[i]) as f64 / (sizes[i + 1] - sizes[i]) as f64;
    for i in 1..sizes.len() - 1 {
        assert_eq!(per_widening(i), per_widening(0), "{samples:?}");
    }
}

#[test]
fn structural_read_graph_registration_keeps_native_version_identity() {
    use crate::kernel::{KernelTermImport, MachineIntegerType, MachineOperandView as V};
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let pointer = address(993180);
    crate::kernel::eval::record_load_access_width(before.memory(), &pointer, 4);
    let named =
        crate::kernel::canonical_form_of_load(before.clone(), pointer.clone(), LoadKind::Int32);
    let beside = intern_memory(before.memory().clone().store(
        Pointer {
            block: "beside-array".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramValue::Int32(var(993182)),
    ));
    let raw = MachineTerm::MemoryLoad(beside, Box::new(pointer.clone()), LoadKind::Int32);
    let root = KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &raw)
        .unwrap();
    let source = KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &named)
        .unwrap();
    let native = EqualityGraph::default().are_int32_equal(&named, &raw);
    assert!(native);
    assert_eq!(
        EqualityGraph::default().are_int32_equal_views(V::Shared(&source), V::Shared(&root)),
        native
    );
    assert_eq!(root.machine_read_leaf(), Some(&raw));
    let changed = MachineTerm::MemoryLoad(
        intern_memory(
            before
                .memory()
                .clone()
                .store(pointer.clone(), ProgramValue::Int32(var(993183))),
        ),
        Box::new(pointer),
        LoadKind::Int32,
    );
    let changed = KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &changed)
        .unwrap();
    assert!(
        !EqualityGraph::default().are_int32_equal_views(V::Shared(&source), V::Shared(&changed))
    );
}

#[test]
fn structural_read_graph_keeps_native_only_stored_values() {
    use crate::kernel::{KernelTermImport, MachineIntegerType, MachineOperandView as V};
    let _session = crate::kernel::VerificationSession::enter();
    let value = MachineTerm::PureFunctionApplication {
        name: "opaque_read_value".into(),
        arguments: vec![var(993184)],
    };
    let pointer = address(993185);
    let retained_state = intern_memory(
        memory()
            .memory()
            .clone()
            .store(pointer.clone(), ProgramValue::Int32(value.clone())),
    );
    let read = MachineTerm::MemoryLoad(retained_state, Box::new(pointer), LoadKind::Int32);
    let shared = KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &read)
        .unwrap();
    assert!(EqualityGraph::default().are_int32_equal_views(V::Shared(&shared), V::Legacy(&value),));
    assert_eq!(shared.machine_read_leaf(), Some(&read));
}
