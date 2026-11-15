//! Deterministic scaling regressions for kernel memory states.
//!
//! A state's maps are persistent and carry cached content hashes, so one
//! store, and interning the state it produces, must cost work logarithmic
//! in the unrelated memory beside it rather than proportional to it. Each
//! test measures charged deterministic work at several sizes and prints the
//! numbers in its assertion messages.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

const SIZES: [usize; 5] = [64, 128, 256, 512, 1024];

#[test]
fn symbolic_stores_into_compact_arrays_scale_with_represented_cells() {
    for bounded in [false, true] {
        let mut samples = Vec::new();
        for count in [4u32, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let source = scaling_cell("local:compact-symbolic-store", 1);
            let beside = scaling_cell("local:compact-symbolic-store", 0);
            let after = source.offset_by_bytes(count * 4);
            let separate = scaling_cell("local:compact-symbolic-separate", 0);
            let value = ProgramValue::UInt32(7u32.into());
            let memory = Memory::new()
                .with_block(source.block.clone(), (count + 2) * 4)
                .with_block(separate.block.clone(), 4)
                .write_scalar_array_region(
                    &source,
                    ProgramType::UInt32,
                    count,
                    value.clone(),
                    false,
                    false,
                    &PureFactContext::new(),
                )
                .unwrap()
                .store(beside.clone(), value.clone())
                .store(after.clone(), value.clone())
                .store(separate.clone(), value.clone());
            let index = MachineTerm::Variable(Variable(925_002));
            let assumptions = if bounded {
                let range = |base: &Pointer, elements: u32| {
                    ResourceFact::own_memory(MemoryRange::new_with_element_width(
                        base.clone(),
                        0u32.into(),
                        elements.into(),
                        4,
                    ))
                };
                let composition = ResourceContext::new()
                    .unchecked_with_fact(range(&beside, 1))
                    .unchecked_with_fact(range(&source, count))
                    .unchecked_with_fact(range(&after, 1));
                PureFactContext::new()
                    .assume_condition(
                        ConditionTerm::signed_less_equal(1u32.into(), index.clone()),
                        true,
                    )
                    .assume_condition(
                        ConditionTerm::signed_less_than(index.clone(), (count - 1).into()),
                        true,
                    )
                    .assume_proposition(Proposition::ResourceComposition(composition))
            } else {
                PureFactContext::new()
            };
            let write = source.offset_by_elements(index, 4);
            let (forgotten, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.without_possible_aliasing_cells(&write, 4, &assumptions)
            });
            assert_eq!(forgotten.known_value(&separate), Some(value.clone()));
            assert!(forgotten.has_initialized_bytes_at(&source, count * 4));
            assert_eq!(forgotten.known_value(&source.offset_by_bytes(4)), None);
            assert_eq!(
                forgotten.known_value(&source.offset_by_bytes((count - 2) * 4)),
                None
            );
            if bounded {
                for kept in [
                    &beside,
                    &source,
                    &source.offset_by_bytes((count - 1) * 4),
                    &after,
                ] {
                    assert_eq!(
                        forgotten.known_value(kept),
                        Some(value.clone()),
                        "bounded store with {count} elements must preserve {kept:?}"
                    );
                }
            } else {
                assert_eq!(forgotten.known_value(&source), None);
                assert_eq!(
                    forgotten.known_value(&source.offset_by_bytes((count - 1) * 4)),
                    None
                );
            }
            samples.push((count, work));
            assert!(
                work <= samples[0].1 * 2 + 128,
                "bounded={bounded}: {samples:?}"
            );
        }
        eprintln!("bounded={bounded}: {samples:?}");
    }
}

#[test]
fn whole_and_partial_stores_into_compact_arrays_visit_live_intervals() {
    for partial in [false, true] {
        let mut samples = Vec::new();
        for count in [4u32, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let source = scaling_cell("local:compact-whole-store", 0);
            let memory = Memory::new()
                .with_block(source.block.clone(), count * 4)
                .write_scalar_array_region(
                    &source,
                    ProgramType::UInt32,
                    count,
                    ProgramValue::UInt32(7u32.into()),
                    false,
                    false,
                    &PureFactContext::new(),
                )
                .unwrap();
            let bytes = count * 4 - u32::from(partial);
            let (forgotten, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.without_possible_aliasing_cells(&source, bytes, &PureFactContext::new())
            });
            assert_eq!(forgotten.known_value(&source), None);
            assert_eq!(
                forgotten.known_value(&source.offset_by_bytes((count - 1) * 4)),
                None
            );
            assert!(forgotten.has_initialized_bytes_at(&source, count * 4));
            samples.push((count, work));
            assert!(
                work <= samples[0].1 * 2 + 64,
                "partial={partial}: {samples:?}"
            );
        }
        eprintln!("partial={partial}: {samples:?}");
    }
}

fn scaling_cell(block: &str, index: usize) -> Pointer {
    Pointer {
        block: PointerBlock::from(block),
        offset: PointerOffsetTerm::Constant(4 * index as i64),
    }
}

fn scaling_value(index: usize) -> ProgramValue {
    ProgramValue::UInt32(MachineTerm::constant(index as u32))
}

/// A memory holding one cell in each of `count` unrelated blocks.
fn memory_with_unrelated_cells(count: usize) -> Memory {
    (0..count).fold(Memory::new(), |memory, index| {
        memory.store(
            scaling_cell(&format!("unrelated-{index}"), 0),
            scaling_value(index),
        )
    })
}

fn log2(size: usize) -> f64 {
    (size as f64).log2()
}

#[test]
fn sequential_stores_scale_as_n_log_n() {
    let mut samples = Vec::new();
    for size in SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
            (0..size).fold(Memory::new(), |memory, index| {
                memory.store(scaling_cell("scaling-heap", index), scaling_value(index))
            })
        });
        assert_eq!(memory.cells.len(), size);
        samples.push((size, work));
    }
    eprintln!("sequential store work (N, units): {samples:?}");
    for (size, work) in &samples {
        assert!(
            (*work as f64) <= 64.0 * *size as f64 * log2(*size),
            "{size} sequential stores charged {work} units, more than 64·N·log2(N): {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        let allowed = (*large as f64 * log2(*large)) / (*small as f64 * log2(*small)) * 1.25;
        let ratio = *large_work as f64 / *small_work as f64;
        assert!(
            ratio <= allowed,
            "sequential store work grew by {ratio:.2} from {small} to {large} stores, \
             above the N·log N ratio {allowed:.2}: {samples:?}"
        );
    }
}

#[test]
fn one_store_is_logarithmic_in_unrelated_cells() {
    let mut samples = Vec::new();
    for size in SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory_with_unrelated_cells(size);
        let (stored, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.store(scaling_cell("store-target", 0), scaling_value(size))
        });
        assert_eq!(stored.cells.len(), size + 1);
        samples.push((size, work));
    }
    eprintln!("one store beside N unrelated cells (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    for (size, work) in &samples {
        let allowed = base_work as f64 + 8.0 * (log2(*size) - log2(smallest));
        assert!(
            (*work as f64) <= allowed,
            "one store beside {size} unrelated cells charged {work} units, \
             above {allowed:.1} (constant plus 8·log2 growth): {samples:?}"
        );
    }
}

#[test]
fn interning_a_one_store_derivative_is_logarithmic_in_unrelated_cells() {
    let mut samples = Vec::new();
    for size in SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let base = memory_with_unrelated_cells(size);
        let interned_base = intern_memory_ref(&base);
        // Derive the state directly rather than through `store`, which
        // would already have interned it while recording its edge.
        let mut derived = base.clone();
        std::sync::Arc::make_mut(&mut derived.cells)
            .insert(scaling_cell("intern-target", 0), scaling_value(size));
        let (interned, work) =
            crate::instrumentation::measure_deterministic_work(|| intern_memory_ref(&derived));
        assert!(interned.arena_id().1 > interned_base.arena_id().1);
        assert_eq!(interned.memory(), &derived);
        samples.push((size, work));
    }
    eprintln!("interning a one-store derivative (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    for (size, work) in &samples {
        let allowed = base_work as f64 + 8.0 * (log2(*size) - log2(smallest));
        assert!(
            (*work as f64) <= allowed,
            "interning a one-store derivative beside {size} unrelated cells charged {work} \
             units, above {allowed:.1} (constant plus 8·log2 growth): {samples:?}"
        );
    }
}

#[test]
fn equal_content_reached_by_different_routes_interns_to_one_id() {
    let mut rehits = Vec::new();
    for size in SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let base = memory_with_unrelated_cells(size);
        let first = scaling_cell("route-target", 0);
        let second = scaling_cell("route-target", 1);
        let forward = base
            .clone()
            .store(first.clone(), scaling_value(1))
            .store(second.clone(), scaling_value(2));
        let backward = base
            .store(second, scaling_value(2))
            .store(first, scaling_value(1));
        // Recording the second route's last store found the first route's
        // state and handed back its storage: equal states carried by
        // execution share roots, so facts embedding them compare in O(1).
        assert!(
            forward.same_storage_roots(&backward),
            "a derivation that reaches interned content must carry the canonical storage"
        );
        // The same content behind storage no derivation produced.
        let backward = backward.with_fresh_storage_roots();
        assert!(
            !forward.same_storage_roots(&backward),
            "the fresh roots must be separate storage for this test to mean anything"
        );
        let forward_id = intern_memory_ref(&forward).arena_id();
        let backward_id = intern_memory_ref(&backward).arena_id();
        assert_eq!(
            forward_id, backward_id,
            "equal content must intern to one arena id at size {size}"
        );
        // The structural hit that deduplicated `backward` registered its
        // storage roots, so asking again is a shallow hit with no comparison.
        let (again, work) =
            crate::instrumentation::measure_deterministic_work(|| intern_memory_ref(&backward));
        assert_eq!(again.arena_id(), forward_id);
        rehits.push((size, work));
    }
    eprintln!("re-interning a deduplicated state (N, units): {rehits:?}");
    assert!(
        rehits.iter().all(|(_, work)| *work == 0),
        "re-interning a structurally deduplicated state must be a shallow hit: {rehits:?}"
    );
}

/// A statement executed twice from one base (planned, then checked) derives
/// the same state twice. The second derivation is recognized as the base's
/// recorded child by comparing only what each changed from the base, and it
/// hands back the child's storage, so facts built from either execution
/// compare by root identity.
#[test]
fn rederiving_a_store_from_one_base_is_logarithmic_and_shares_storage() {
    let mut samples = Vec::new();
    for size in SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let base = memory_with_unrelated_cells(size);
        let first = base
            .clone()
            .store(scaling_cell("rederived", 0), scaling_value(size));
        let (second, work) = crate::instrumentation::measure_deterministic_work(|| {
            base.clone()
                .store(scaling_cell("rederived", 0), scaling_value(size))
        });
        assert!(
            first.same_storage_roots(&second),
            "the second derivation must carry the first one's storage at size {size}"
        );
        samples.push((size, work));
    }
    eprintln!("re-deriving one store beside N unrelated cells (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    for (size, work) in &samples {
        let allowed = base_work as f64 + 8.0 * (log2(*size) - log2(smallest));
        assert!(
            (*work as f64) <= allowed,
            "re-deriving one store beside {size} unrelated cells charged {work} units, \
             above {allowed:.1} (constant plus 8·log2 growth): {samples:?}"
        );
    }
}

/// Normalizing a resource context visits, for each allocation token, only
/// the tokens that could name the same block: tokens anchored in distinct
/// heap blocks never merge, so they are not paired.
#[test]
fn normalizing_allocation_tokens_in_distinct_heap_blocks_is_linear() {
    let mut samples = Vec::new();
    for size in SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let resources = (0..size as u64).fold(ResourceContext::new(), |resources, identity| {
            resources.unchecked_with_fact(ResourceFact::own_allocation(heap_cell(identity, 0), 4))
        });
        let assumptions = PureFactContext::new();
        let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.normalized(&assumptions)
        });
        assert_eq!(normalized.facts().len(), size);
        samples.push((size, work));
    }
    eprintln!("normalizing N allocation tokens (N, units): {samples:?}");
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        assert!(
            *large_work <= small_work * (large / small) + 16,
            "normalization work grew from {small_work} to {large_work} units between \
             {small} and {large} tokens, faster than linear: {samples:?}"
        );
    }
}

/// [`normalizing_allocation_tokens_in_distinct_heap_blocks_is_linear`] with
/// 64-bit tokens: a `uint64` byte count does not pair tokens either.
#[test]
fn normalizing_64_bit_allocation_tokens_in_distinct_heap_blocks_is_linear() {
    let mut samples = Vec::new();
    for size in SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let resources = (0..size as u64).fold(ResourceContext::new(), |resources, identity| {
            let count = MachineTerm::Variable(Variable((1 << 40) + identity));
            resources.unchecked_with_fact(ResourceFact::own_heap_allocation(
                heap_cell(identity, 0),
                &wide_heap_extent(&count),
            ))
        });
        let assumptions = PureFactContext::new();
        let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.normalized(&assumptions)
        });
        assert_eq!(normalized.facts().len(), size);
        samples.push((size, work));
    }
    eprintln!("normalizing N 64-bit allocation tokens (N, units): {samples:?}");
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        assert!(
            *large_work <= small_work * (large / small) + 16,
            "normalization work grew from {small_work} to {large_work} units between \
             {small} and {large} 64-bit tokens, faster than linear: {samples:?}"
        );
    }
}

// Operations on one heap allocation beside `N` unrelated live allocations.
//
// Every `Heap` identity is proven distinct from every other block identity
// except a symbolic one, so a store, havoc, free or load through one
// allocation may visit only that allocation's entries and the symbolic ones
// (`AliasCandidates`). Each test below measures one such operation at several
// allocation counts and bounds its growth by a constant plus a logarithm.

const HEAP_SIZES: [usize; 4] = [16, 64, 256, 1024];

/// The identity of the allocation the measured operation targets; the
/// unrelated ones take identities below it.
const TARGET_HEAP: u64 = 1_000_000;

fn heap_cell(identity: u64, offset: i64) -> Pointer {
    Pointer {
        block: PointerBlock::Heap(identity),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

/// A successful 16-byte `malloc` at `identity` whose first word is written.
fn with_initialized_allocation(memory: Memory, identity: u64, value: u32) -> Memory {
    let pending = Pointer {
        block: PointerBlock::Symbolic(Variable(identity)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let (memory, _, base) = memory
        .with_pending_heap_allocation(pending.clone(), HeapExtent::int32(16), false)
        .resolve_pending_heap_allocation(&pending, true)
        .expect("the pending allocation resolves");
    assert_eq!(base, heap_cell(identity, 0));
    memory.store(base, ProgramValue::UInt32(MachineTerm::constant(value)))
}

/// `unrelated` live allocations, each holding one initialized cell, and the
/// target allocation with its first word written.
fn memory_with_unrelated_allocations(unrelated: usize) -> Memory {
    let memory = (0..unrelated).fold(Memory::new(), |memory, index| {
        with_initialized_allocation(memory, index as u64 + 1, index as u32)
    });
    with_initialized_allocation(memory, TARGET_HEAP, 7)
}

fn assert_constant_plus_log_growth(what: &str, samples: &[(usize, usize)], slope: f64) {
    eprintln!("{what} (N, units): {samples:?}");
    let (smallest, base_work) = samples[0];
    for (size, work) in samples {
        let allowed = base_work as f64 + slope * (log2(*size) - log2(smallest));
        assert!(
            (*work as f64) <= allowed,
            "{what}: {size} unrelated allocations charged {work} units, above {allowed:.1} \
             (constant plus {slope}·log2 growth): {samples:?}"
        );
    }
}

#[test]
fn one_heap_store_is_logarithmic_in_unrelated_allocations() {
    let mut samples = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory_with_unrelated_allocations(size);
        // Only the target is owned: the resource side's own scaling is
        // measured end to end in `src/scaling_tests/surface/tests/scaling_tests.rs`.
        let resources =
            ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                heap_cell(TARGET_HEAP, 0),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            )));
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let statement = ProgramStatement::TypedStore {
            access_class: None,
            pointer: ProgramExpression::Value(ProgramValue::typed_pointer(
                heap_cell(TARGET_HEAP, 4),
                ProgramType::UInt32Pointer,
            )),
            value: ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::constant(9))),
            value_type: ProgramType::UInt32,
            volatile: false,
            pointee_constant: false,
            source: Default::default(),
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_execution_statement_paths(
                &state,
                &statement,
                &PureFactContext::new(),
                ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        let StatementOutcome::Normal(stored) = &paths[0].outcome else {
            panic!("the heap store executes: {:?}", paths[0].outcome);
        };
        assert_eq!(stored.memory().cells.len(), size + 2);
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("one C store into a heap block", &samples, 16.0);
}

/// `n * 4` bytes for a symbolic `size_t` count `n`: a 64-bit extent
/// (`design/heap-extents.md`, stage 2).
fn wide_heap_extent(count: &MachineTerm) -> HeapExtent {
    HeapExtent::new(
        MachineTerm::uint64_multiply(count.clone(), MachineTerm::uint64_constant(4)),
        HeapExtentKind::UInt64,
    )
}

/// The wide owned range `base[0..count]` of `uint32` elements.
fn wide_heap_range(identity: u64, count: &MachineTerm) -> MemoryRange {
    MemoryRange::new_wide(
        heap_cell(identity, 0),
        MachineTerm::uint64_constant(0),
        count.clone(),
        4,
    )
}

/// [`one_heap_store_is_logarithmic_in_unrelated_allocations`] over 64-bit
/// blocks: every block, the target included, has a symbolic `size_t`
/// element count and is owned by a wide range, which the interval index
/// does not hold, and the store's index is a `size_t` the facts bound by
/// the target's count. Finding the target's range and forming the pointer
/// against its 64-bit extent must not visit the unrelated ones.
#[test]
fn one_store_into_a_64_bit_heap_block_is_logarithmic_in_unrelated_64_bit_allocations() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let count = |identity: u64| MachineTerm::Variable(Variable((1 << 40) + identity));
        let index = MachineTerm::Variable(Variable(1 << 41));
        // The allocation's admission bound and the store's index bound.
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    count(TARGET_HEAP),
                    MachineTerm::uint64_constant(i64::MAX as u64 / 4),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_than(index.clone(), count(TARGET_HEAP)),
                true,
            );
        let allocate = |(memory, resources): (Memory, ResourceContext), identity: u64| {
            let pending = Pointer {
                block: PointerBlock::Symbolic(Variable(identity)),
                offset: PointerOffsetTerm::Constant(0),
            };
            let (memory, _, base) = memory
                .with_pending_heap_allocation(
                    pending.clone(),
                    wide_heap_extent(&count(identity)),
                    false,
                )
                .resolve_pending_heap_allocation(&pending, true)
                .expect("the pending allocation resolves");
            assert_eq!(base, heap_cell(identity, 0));
            let resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                wide_heap_range(identity, &count(identity)),
            ));
            (memory, resources)
        };
        let (memory, resources) = (1..=size as u64).chain([TARGET_HEAP]).fold(
            (
                Memory::new(),
                ResourceContext::new_with_equalities(&assumptions),
            ),
            allocate,
        );
        resources.synchronize_memory_equalities(&assumptions);
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let statement = ProgramStatement::TypedStore {
            access_class: None,
            pointer: ProgramExpression::Add(
                Box::new(ProgramExpression::Value(ProgramValue::typed_pointer(
                    heap_cell(TARGET_HEAP, 0),
                    ProgramType::UInt32Pointer,
                ))),
                Box::new(ProgramExpression::Value(ProgramValue::UInt64(
                    index.clone(),
                ))),
            ),
            value: ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::constant(9))),
            value_type: ProgramType::UInt32,
            volatile: false,
            pointee_constant: false,
            source: Default::default(),
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_execution_statement_paths(
                &state,
                &statement,
                &assumptions,
                ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        let StatementOutcome::Normal(_) = &paths[0].outcome else {
            panic!("the wide heap store executes: {:?}", paths[0].outcome);
        };
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("one C store into a 64-bit heap block", &samples, 16.0);
}

/// [`one_store_into_a_64_bit_heap_block_is_logarithmic_in_unrelated_64_bit_allocations`]
/// for a field of a struct-array block: every block holds `m * 8u64` bytes
/// of eight-byte structs, owned as a wide byte range, and the store writes
/// the second field of element `i`, `*byte_offset(p + (int64)i * 8, 4)`.
/// Placing the field over the element count (formation against the extent,
/// membership in the byte range) must not visit the unrelated blocks.
#[test]
fn one_field_store_into_a_64_bit_struct_array_block_is_logarithmic_in_unrelated_blocks() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let count = |identity: u64| MachineTerm::Variable(Variable((1 << 40) + identity));
        let bytes = |identity: u64| {
            MachineTerm::uint64_multiply(count(identity), MachineTerm::uint64_constant(8))
        };
        let index = MachineTerm::Variable(Variable(1 << 41));
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    count(TARGET_HEAP),
                    MachineTerm::uint64_constant(i64::MAX as u64 / 8),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_than(index.clone(), count(TARGET_HEAP)),
                true,
            );
        let allocate = |(memory, resources): (Memory, ResourceContext), identity: u64| {
            let pending = Pointer {
                block: PointerBlock::Symbolic(Variable(identity)),
                offset: PointerOffsetTerm::Constant(0),
            };
            let (memory, _, base) = memory
                .with_pending_heap_allocation(
                    pending.clone(),
                    HeapExtent::new(bytes(identity), HeapExtentKind::UInt64),
                    false,
                )
                .resolve_pending_heap_allocation(&pending, true)
                .expect("the pending allocation resolves");
            assert_eq!(base, heap_cell(identity, 0));
            let resources =
                resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new_wide(
                    heap_cell(identity, 0),
                    MachineTerm::uint64_constant(0),
                    bytes(identity),
                    1,
                )));
            (memory, resources)
        };
        let (memory, resources) = (1..=size as u64).chain([TARGET_HEAP]).fold(
            (
                Memory::new(),
                ResourceContext::new_with_equalities(&assumptions),
            ),
            allocate,
        );
        resources.synchronize_memory_equalities(&assumptions);
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let element = ProgramExpression::Add(
            Box::new(ProgramExpression::Value(ProgramValue::typed_pointer(
                heap_cell(TARGET_HEAP, 0),
                ProgramType::UInt8Pointer,
            ))),
            Box::new(ProgramExpression::Value(ProgramValue::Int64(
                MachineTerm::int64_multiply(index.clone(), MachineTerm::int64_constant(8)),
            ))),
        );
        let statement = ProgramStatement::TypedStore {
            access_class: None,
            pointer: ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(element),
                bytes: 4,
            },
            value: ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::constant(9))),
            value_type: ProgramType::UInt32,
            volatile: false,
            pointee_constant: false,
            source: Default::default(),
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_execution_statement_paths(
                &state,
                &statement,
                &assumptions,
                ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        let StatementOutcome::Normal(_) = &paths[0].outcome else {
            panic!("the struct field store executes: {:?}", paths[0].outcome);
        };
        samples.push((size, work));
    }
    assert_constant_plus_log_growth(
        "one field store into a 64-bit struct-array block",
        &samples,
        16.0,
    );
}

#[test]
fn one_classed_heap_store_and_read_are_logarithmic_in_recorded_effective_types() {
    // Every unrelated allocation's first word, and every other word of the
    // target, carries a recorded effective type; recording the target's
    // store and checking a read of it touch only the target's neighbours.
    use crate::kernel::effective_type::{CAccessClass, CScalarClass};
    const INT: CAccessClass = CAccessClass::Scalar(CScalarClass::Int);
    let mut stores = Vec::new();
    let mut reads = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = memory_with_unrelated_allocations(size);
        for index in 0..size {
            let cell = heap_cell(index as u64 + 1, 0);
            let value = ProgramValue::UInt32(MachineTerm::constant(index as u32));
            memory = memory.with_heap_effective_type(&cell, 4, Some(INT), &value);
        }
        let resources =
            ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                heap_cell(TARGET_HEAP, 0),
                MachineTerm::constant(0),
                MachineTerm::constant(8),
            )));
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let pointer = ProgramExpression::Value(ProgramValue::typed_pointer(
            heap_cell(TARGET_HEAP, 4),
            ProgramType::UInt32Pointer,
        ));
        let store = ProgramStatement::TypedStore {
            access_class: Some(INT),
            pointer: pointer.clone(),
            value: ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::constant(9))),
            value_type: ProgramType::UInt32,
            volatile: false,
            pointee_constant: false,
            source: Default::default(),
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_execution_statement_paths(
                &state,
                &store,
                &PureFactContext::new(),
                ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        let StatementOutcome::Normal(stored) = &paths[0].outcome else {
            panic!("the heap store executes: {:?}", paths[0].outcome);
        };
        assert_eq!(
            stored
                .memory()
                .heap_effective_class(&heap_cell(TARGET_HEAP, 4)),
            Some(INT)
        );
        stores.push((size, work));
        let read = ProgramExpression::TypedLoad {
            pointer: Box::new(pointer),
            value_type: ProgramType::UInt32,
            volatile: false,
            pointee_constant: false,
            access_class: Some(INT),
            source: Default::default(),
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::eval::evaluate_program_expression_paths(
                stored,
                &read,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert!(matches!(paths[0].outcome, ExpressionOutcome::Value(_)));
        reads.push((size, work));
    }
    assert_constant_plus_log_growth("one classed C store into a heap block", &stores, 16.0);
    assert_constant_plus_log_growth("one checked read of a typed heap cell", &reads, 16.0);
}

fn target_range() -> MemoryRange {
    MemoryRange::new_with_element_width(
        heap_cell(TARGET_HEAP, 0),
        MachineTerm::constant(0),
        MachineTerm::constant(16),
        1,
    )
}

#[test]
fn one_call_havoc_and_its_check_are_logarithmic_in_unrelated_allocations() {
    let mut produced = Vec::new();
    let mut checked = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory_with_unrelated_allocations(size);
        let ranges = [target_range()];
        let assumptions = PureFactContext::new();
        let (havocked, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.clone().with_call_memory_havoc(
                Variable(TARGET_HEAP + 1),
                &ranges,
                &assumptions,
                None,
            )
        });
        assert_eq!(
            havocked.cells.len(),
            size,
            "only the target's cell is dropped"
        );
        produced.push((size, work));
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            havocked.matches_call_memory_havoc_result(&memory, &ranges, &assumptions, None)
        });
        assert!(matches, "the checker accepts the producer's result");
        checked.push((size, work));
    }
    assert_constant_plus_log_growth("one call havoc of a heap range", &produced, 16.0);
    assert_constant_plus_log_growth("checking one call havoc of a heap range", &checked, 16.0);
}

#[test]
fn one_free_is_logarithmic_in_unrelated_allocations() {
    let mut samples = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory_with_unrelated_allocations(size);
        let assumptions = PureFactContext::new();
        let (freed, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory
                .clone()
                .free_heap_block(&heap_cell(TARGET_HEAP, 0), &assumptions)
        });
        let freed = freed.expect("the target allocation frees");
        assert_eq!(freed.cells.len(), size);
        assert_eq!(freed.heap.live_allocations.len(), size);
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("one free of a heap block", &samples, 16.0);
}

#[test]
fn one_heap_load_is_logarithmic_in_unrelated_allocations() {
    let mut known = Vec::new();
    let mut unknown = Vec::new();
    for size in HEAP_SIZES {
        // The unrelated allocations are fresh; the target is a contract
        // claim, so a cell the memory does not know reads as a named load
        // rather than an uninitialized one, and takes the full load path.
        //
        // The memory is built in a session of its own. Naming a load walks
        // the derivation history back to the cell's last write (the
        // resource tracker's cell version walk), which is work in the length
        // of the history, one edge per transition, not in the size of the
        // memory. Measuring in a fresh session leaves that walk nothing to
        // cross, so what remains is the load's own work beside `size`
        // unrelated allocations.
        let memory = {
            let _build = crate::kernel::VerificationSession::enter();
            (0..size)
                .fold(Memory::new(), |memory, index| {
                    with_initialized_allocation(memory, index as u64 + 1, index as u32)
                })
                .with_heap_allocation_claim(heap_cell(TARGET_HEAP, 0), HeapExtent::int32(16))
                .expect("the claim registers")
                .store(
                    heap_cell(TARGET_HEAP, 0),
                    ProgramValue::UInt32(MachineTerm::constant(7)),
                )
        };
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let load = |offset| {
            crate::instrumentation::measure_deterministic_work(|| {
                evaluate_memory_load_paths(
                    &memory,
                    heap_cell(TARGET_HEAP, offset),
                    ProgramType::UInt32,
                    Vec::new().into(),
                    Vec::new(),
                    &assumptions,
                    false,
                    false,
                    None,
                    None,
                )
            })
        };
        let (paths, work) = load(0);
        assert_eq!(paths.len(), 1);
        assert_eq!(
            paths[0].outcome,
            ExpressionOutcome::Value(ProgramValue::UInt32(MachineTerm::constant(7)))
        );
        known.push((size, work));
        let (paths, work) = load(8);
        assert_eq!(paths.len(), 1, "{paths:?}");
        assert!(
            matches!(paths[0].outcome, ExpressionOutcome::Value(_)),
            "{:?}",
            paths[0].outcome
        );
        unknown.push((size, work));
    }
    assert_constant_plus_log_growth("one load of a known heap cell", &known, 16.0);
    assert_constant_plus_log_growth("one load of an unknown heap cell", &unknown, 16.0);
}

/// Every pointer parameter lives in the one `ExternalArgument` block, so
/// neither the alias-candidate ranges nor the block-pair separation index
/// narrow a store through one parameter: each cached field of every other
/// parameter is a candidate. `count` parameter objects each have one cached
/// field, and the store goes through a borrowed field-bearing region (its
/// header object and its data range are two more owned members of the same
/// composition, like `examples/arena`'s `arena_write`).
fn owned_parameter_objects_and_a_region_store(
    count: usize,
) -> (Memory, PureFactContext, Pointer, Vec<Pointer>) {
    let parameter = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(id)), 4),
    };
    let objects = (0..count)
        .map(|index| parameter(97_000 + index as u64))
        .collect::<Vec<_>>();
    let region = parameter(97_900);
    let data = parameter(97_901);
    let length = MachineTerm::Variable(Variable(97_902));
    let index = MachineTerm::Variable(Variable(97_903));
    let field = |object: &Pointer| object.offset_by_elements(MachineTerm::constant(1), 4);
    let mut cells = objects.iter().map(field).collect::<Vec<_>>();
    cells.push(field(&region));
    let memory = cells
        .iter()
        .enumerate()
        .fold(Memory::new(), |memory, (value, cell)| {
            memory.store(cell.clone(), scaling_value(value))
        });
    let object_range = |base: &Pointer, elements: u32| {
        MemoryRange::new(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(elements),
        )
    };
    let composition = objects
        .iter()
        .map(|object| ResourceFact::own_memory(object_range(object, 2)))
        .chain([
            ResourceFact::own_memory(object_range(&region, 3)),
            ResourceFact::own_memory(MemoryRange::new(
                data.clone(),
                MachineTerm::constant(0),
                length.clone(),
            )),
        ])
        .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index.clone(), length), true)
        .assume_proposition(Proposition::ResourceComposition(composition));
    let write = data.offset_by_elements(index, 4);
    (memory, assumptions, write, cells)
}

/// A store through a borrowed region beside `N` cached fields of other owned
/// parameter objects. Ownership separates every one of them, and it is
/// asked first through each composition's base index, so the store pays a
/// small constant per cached cell (visiting it at all is the alias-candidate
/// walk) and never the pure-fact distinctness ladder, whose failing searches
/// cost work in every separation fact of the block. Measured: 96, 160, 288
/// and 544 units at 4, 8, 16 and 32 cells (16 per cell). Before ownership
/// was asked first, the ladder charged 376, 1508, 8732 and 60940: each
/// failing search walked the composition's pairwise separations, which grow
/// with the square of the owned objects.
#[test]
fn a_store_beside_owned_parameter_fields_is_linear_in_the_cached_cells() {
    let mut samples = Vec::new();
    for count in [4, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, assumptions, write, cells) = owned_parameter_objects_and_a_region_store(count);
        let (stored, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.without_possible_aliasing_cells(&write, 4, &assumptions)
        });
        for cell in &cells {
            assert!(
                stored.has_known_cell_at(cell),
                "ownership separates {cell:?} from the store at {write:?}"
            );
        }
        samples.push((count, work));
    }
    eprintln!("region store beside N owned parameter fields (N, units): {samples:?}");
    for (count, work) in &samples {
        assert!(
            *work <= 20 * count + 100,
            "a store beside {count} owned parameter fields charged {work} units, \
             above 20·N + 100: {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        let ratio = *large_work as f64 / *small_work as f64;
        assert!(
            ratio <= 2.25,
            "store work grew by {ratio:.2} from {small} to {large} cached cells, \
             above linear: {samples:?}"
        );
    }
}

/// The comparison the `ExternalArgument` family is measured against: the
/// same number of cached fields, all in one heap object, beside a store into
/// another field of it. Constant offsets in one block decide every pair on
/// the first rung: 22, 42, 82 and 162 units at 4, 8, 16 and 32 cells.
#[test]
fn a_store_beside_fields_of_one_heap_object_is_linear_in_the_cached_cells() {
    let mut samples = Vec::new();
    for count in [4, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let cells = (0..count)
            .map(|index| heap_cell(3, 4 * index as i64))
            .collect::<Vec<_>>();
        let memory = cells
            .iter()
            .enumerate()
            .fold(Memory::new(), |memory, (value, cell)| {
                memory.store(cell.clone(), scaling_value(value))
            });
        let write = heap_cell(3, 4 * count as i64);
        let (stored, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.without_possible_aliasing_cells(&write, 4, &PureFactContext::new())
        });
        for cell in &cells {
            assert!(stored.has_known_cell_at(cell));
        }
        samples.push((count, work));
    }
    eprintln!("heap store beside N fields of its own object (N, units): {samples:?}");
    for (count, work) in &samples {
        assert!(
            *work <= 8 * count + 32,
            "a heap store beside {count} fields charged {work} units: {samples:?}"
        );
    }
}

/// After N consecutive contract calls that each consume and produce an
/// allocation-bearing composite (a call havoc over the owner and its
/// allocation, the retirement of that allocation, and the claim for the one
/// it returns), the call rule's retirement check and the walks that name the
/// owner's field, the new allocation's cell and the owner's block all stop
/// at the last call. So each call costs the same, and N calls cost linear
/// work: an earlier call is never re-examined. The sizes use disjoint
/// variables, so no state or memo is shared between them.
#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn consecutive_reallocating_calls_cost_the_same_each() {
    const CALLS: [usize; 4] = [16, 64, 256, 1024];
    let external = |variable: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(variable)), 4),
    };
    let int32_range = |base: &Pointer, end: u32| {
        MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(end),
            4,
        )
    };
    let bytes = MachineTerm::constant(4);
    let assumptions = PureFactContext::new();
    let mut last_call_samples = Vec::new();
    let mut total_samples = Vec::new();
    for (size_index, calls) in CALLS.into_iter().enumerate() {
        let variables = 5_100_000 + 10_000 * size_index as u64;
        let owner = external(variables);
        let field = owner.offset_by_bytes(0);
        let other = external(variables + 1);
        let data = |call: usize| external(variables + 2 + call as u64);
        let kept = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(int32_range(&other, 2)));
        let mut memory = Memory::new();
        let mut total = 0;
        let mut last = 0;
        for call in 0..calls {
            let ranges = vec![int32_range(&owner, 2), int32_range(&data(call), 1)];
            let lent = ResourceContext::new()
                .unchecked_with_facts(ranges.iter().cloned().map(ResourceFact::own_memory));
            let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
                let stale = crate::kernel::functions::caller_resource_left_stale_by_retirement(
                    &lent,
                    &kept,
                    &data(call),
                    &HeapExtent::int32(bytes.clone()),
                    &assumptions,
                )
                .cloned();
                assert_eq!(stale, None, "the lent owner covers the retired allocation");
                let next = memory
                    .clone()
                    .with_call_memory_havoc(
                        Variable(variables + 5_000 + call as u64),
                        &ranges,
                        &assumptions,
                        None,
                    )
                    .retire_contract_heap_allocation_claim(&data(call), &bytes, &assumptions)
                    .with_heap_allocation_claim(data(call + 1), HeapExtent::int32(bytes.clone()))
                    .expect("a fresh claim");
                let point =
                    crate::kernel::resource_tracker::VersionPoint::at(&intern_memory_ref(&next));
                for cell in [&field, &data(call + 1)] {
                    crate::kernel::resource_tracker::last_same_version_point(
                        crate::kernel::resource_tracker::TrackedResource::Cell {
                            pointer: cell,
                            bytes: 4,
                        },
                        &point,
                    );
                }
                crate::kernel::resource_tracker::last_same_version_point(
                    crate::kernel::resource_tracker::TrackedResource::Block(
                        &PointerBlock::ExternalArgument,
                    ),
                    &point,
                );
                next
            });
            memory = next;
            total += work;
            last = work;
        }
        // The field is named at the last call's havoc, not at any earlier one.
        let named = crate::kernel::resource_tracker::last_same_version_point(
            crate::kernel::resource_tracker::TrackedResource::Cell {
                pointer: &field,
                bytes: 4,
            },
            &crate::kernel::resource_tracker::VersionPoint::at(&intern_memory_ref(&memory)),
        )
        .expect("the walk has an answer");
        assert!(
            matches!(
                named.shared_memory().derivation().as_deref(),
                Some(MemoryDerivation::CallHavoc { .. })
            ),
            "the field is named at the last call's havoc"
        );
        last_call_samples.push((calls, last));
        total_samples.push((calls, total));
    }
    assert_constant_plus_log_growth("the last of N reallocating calls", &last_call_samples, 4.0);
    // Linear in N: the per-call average does not grow.
    let (smallest, smallest_total) = total_samples[0];
    let per_call = smallest_total as f64 / smallest as f64;
    for (calls, total) in &total_samples {
        assert!(
            *total as f64 <= (per_call + 4.0) * *calls as f64,
            "{calls} reallocating calls charged {total} units, above {:.1} per call: \
             {total_samples:?}",
            per_call + 4.0
        );
    }
}

/// The retirement check admits a kept view of exactly the bytes of a kept
/// owned range by one exact lookup, when the lent owners cover the retired
/// allocation: the caller's own object is disjoint from what it lent, so the
/// view it holds of that object is too. This is the view `examples/arena`'s
/// pipeline keeps of a region descriptor that `arena_free` returned, beside
/// the `arena_destroy` that frees the backing arrays; the general separation
/// search it used to take cost millions of units there. A view without that
/// owner, or with lent owners that do not cover the allocation, still needs a
/// proved separation.
#[test]
fn retirement_admits_a_view_of_a_kept_owned_range() {
    let external = |variable: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(variable)), 4),
    };
    let int32_range = |base: &Pointer, end: u32| {
        MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(end),
            4,
        )
    };
    let data = external(5_300_000);
    let descriptor = external(5_300_001);
    let bytes = MachineTerm::constant(8);
    let assumptions = PureFactContext::new();
    let lent =
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(int32_range(&data, 2)));
    let view = ResourceFact::view_memory(int32_range(&descriptor, 3));
    let owned_and_viewed = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(int32_range(&descriptor, 3)))
        .unchecked_with_fact(view.clone());
    let (stale, work) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::functions::caller_resource_left_stale_by_retirement(
            &lent,
            &owned_and_viewed,
            &data,
            &HeapExtent::int32(bytes.clone()),
            &assumptions,
        )
        .cloned()
    });
    assert_eq!(stale, None, "the view names only bytes the caller owns");
    assert!(
        work <= 64,
        "the view's owner is one lookup, not a search: {work} units"
    );

    let viewed_only = ResourceContext::new().unchecked_with_fact(view.clone());
    assert_eq!(
        crate::kernel::functions::caller_resource_left_stale_by_retirement(
            &lent,
            &viewed_only,
            &data,
            &HeapExtent::int32(bytes.clone()),
            &assumptions,
        ),
        Some(&view),
        "a view the caller does not own may alias the retired allocation"
    );
    assert!(
        crate::kernel::functions::caller_resource_left_stale_by_retirement(
            &ResourceContext::new(),
            &owned_and_viewed,
            &data,
            &HeapExtent::int32(bytes.clone()),
            &assumptions,
        )
        .is_some(),
        "without lent owners covering the allocation, the kept object needs a separation"
    );
}

/// `count` unrelated atomic condition facts: a bound and an equality over
/// fresh variables for each index, the ambient facts a long proof path
/// accumulates about objects a query does not name.
fn unrelated_condition_facts(count: usize) -> PureFactContext {
    (0..count as u64).fold(PureFactContext::new(), |facts, index| {
        let variable = |offset: u64| MachineTerm::Variable(Variable(96_000 + 3 * index + offset));
        facts
            .assume_condition(
                ConditionTerm::signed_less_equal(variable(0), MachineTerm::constant(1_000)),
                true,
            )
            .assume_condition(ConditionTerm::equal(variable(1), variable(2)), true)
    })
}

/// A condition-fact query reads the fact it asks about by key: the fact
/// itself, a fact filed under a spelling its sides' equality classes make
/// equal, or none at all, beside `N` unrelated facts. Each of the three
/// queries used to scan every condition fact (uncharged, so only the visit
/// counter shows it): 2N visits per query on the base. The symbolic
/// pointer-equality hop of range membership reads the equalities naming its
/// pointer, and the ordering modulo canonical load atoms reads the facts
/// filed under the query's canonical sides.
#[test]
fn condition_fact_queries_ignore_unrelated_facts() {
    let (low, high, alias) = (
        MachineTerm::Variable(Variable(95_001)),
        MachineTerm::Variable(Variable(95_002)),
        MachineTerm::Variable(Variable(95_003)),
    );
    let symbolic = Pointer {
        block: PointerBlock::Symbolic(Variable(95_004)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let argument = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(95_005)), 4),
    };
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let facts = unrelated_condition_facts(size)
            .assume_condition(
                ConditionTerm::signed_less_than(low.clone(), high.clone()),
                true,
            )
            .assume_condition(ConditionTerm::equal(alias.clone(), low.clone()), true)
            .assume_condition(
                ConditionTerm::pointer_equal(symbolic.clone(), argument.clone()),
                true,
            );
        let visits = |query: &dyn Fn() -> bool, expected: bool| {
            PureFactContext::reset_condition_fact_visits();
            assert_eq!(query(), expected);
            PureFactContext::condition_fact_visits()
        };
        let exact = visits(
            &|| {
                facts.has_condition_fact(
                    ConditionTerm::signed_less_than(low.clone(), high.clone()),
                    true,
                )
            },
            true,
        );
        let through_class = visits(
            &|| {
                facts.has_condition_fact(
                    ConditionTerm::signed_less_than(alias.clone(), high.clone()),
                    true,
                )
            },
            true,
        );
        let miss = visits(
            &|| {
                facts.has_condition_fact(
                    ConditionTerm::signed_less_than(high.clone(), low.clone()),
                    true,
                )
            },
            false,
        );
        let canonical = visits(
            &|| {
                facts.exact_ordering_modulo_canonical_atoms(&ConditionTerm::signed_less_than(
                    low.clone(),
                    high.clone(),
                ))
            },
            true,
        );
        let hop = visits(
            &|| {
                facts.pointer_in_range_with_width(
                    &symbolic,
                    &argument,
                    &MachineTerm::constant(0),
                    &MachineTerm::constant(1),
                    4,
                )
            },
            true,
        );
        samples.push((size, exact + through_class + miss + canonical + hop));
    }
    eprintln!("condition-fact queries beside N unrelated facts (N, visits): {samples:?}");
    assert!(
        samples
            .iter()
            .all(|(_, visits)| *visits == samples[0].1 && *visits <= 8),
        "condition-fact queries visited unrelated facts: {samples:?}"
    );
}

/// An object reached through a parameter: every such object shares the
/// `ExternalArgument` block and differs by a symbolic base, as the arena's
/// descriptors do, so no block distinctness separates them.
fn external_object(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(identity)), 4),
    }
}

fn external_field(identity: u64, bytes: i64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Add(
            Box::new(external_object(identity).offset),
            Box::new(PointerOffsetTerm::Constant(bytes)),
        ),
    }
}

fn external_range(identity: u64, start: u32, end: u32) -> MemoryRange {
    MemoryRange::new(
        external_object(identity),
        MachineTerm::constant(start),
        MachineTerm::constant(end),
    )
}

/// One call havoc lending `external_range(LENT, 0, 16)` from a caller whose
/// residual is `residual`, beside a cached cell of the kept member `KEPT`:
/// the producer's and the checker's work, after asserting that the edge
/// records both `KEPT` and the uncached member `UNCACHED`.
fn kept_call_havoc_work(residual: ResourceContext) -> (usize, usize) {
    const LENT: u64 = 3_000_000;
    let assumptions = PureFactContext::new();
    let kept = CallKeptOwnership::new(
        residual,
        CallKeptRanges::new(ResourceContext::new(), Vec::new(), None),
        &assumptions,
    );
    let memory = Memory::new().store(
        external_field(KEPT_MEMBER, 8),
        ProgramValue::Int32(MachineTerm::constant(5)),
    );
    // The callee's footprint shares the parameters' block, so the
    // separation rule cannot keep the cell on its own.
    let ranges = [external_range(LENT, 0, 16)];
    let (havocked, produced) = crate::instrumentation::measure_deterministic_work(|| {
        memory.clone().with_call_memory_havoc(
            Variable(LENT + 1),
            &ranges,
            &assumptions,
            Some(&kept),
        )
    });
    // Whole cells held by the caller's flat frame stay cached. The edge
    // also retains uncached members so later reads can cross this call.
    assert!(havocked.has_known_cell_at(&external_field(KEPT_MEMBER, 8)));
    let recorded = CallKeptRanges::recorded_on(&havocked).expect("the call records kept memory");
    assert!(
        recorded.holds_access(&external_field(KEPT_MEMBER, 8), 4, &assumptions),
        "the residual member that holds the cached cell is recorded on the edge"
    );
    assert!(
        recorded.holds_access(&external_field(UNCACHED_MEMBER, 0), 4, &assumptions),
        "a residual member with no cached cell is recorded on the edge too"
    );
    let (matches, checked) = crate::instrumentation::measure_deterministic_work(|| {
        havocked.matches_call_memory_havoc_result(&memory, &ranges, &assumptions, Some(&kept))
    });
    assert!(matches, "the checker re-derives the kept ranges");
    let dropped =
        memory
            .clone()
            .with_call_memory_havoc(Variable(LENT + 1), &ranges, &assumptions, None);
    assert!(
        CallKeptRanges::recorded_on(&dropped).is_none(),
        "without the residual nothing is recorded as kept"
    );
    (produced, checked)
}

const KEPT_MEMBER: u64 = 2_000_000;
const UNCACHED_MEMBER: u64 = 2_100_000;

/// The two members every [`kept_call_havoc_work`] residual keeps: one with a
/// cached cell and one without.
fn measured_kept_members() -> [ResourceFact; 2] {
    [
        ResourceFact::own_memory(external_range(KEPT_MEMBER, 0, 12)),
        ResourceFact::own_memory(external_range(UNCACHED_MEMBER, 0, 4)),
    ]
}

/// A call havoc records the flat members its caller keeps owning from the
/// residual's per-block owned-memory index over the blocks its write set
/// may alias, whether or not a member's cell is cached. Residual resources
/// that cannot alias the footprint -- owned memory in heap blocks, which are
/// proven distinct from the parameters' block, and views, which keep nothing
/// -- add no work to the producer or to its checker.
#[test]
fn a_call_records_kept_members_without_visiting_unrelated_residual_resources() {
    let mut produced = Vec::new();
    let mut checked = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let residual = ResourceContext::new().unchecked_with_facts(
            (0..size)
                .flat_map(|index| {
                    [
                        ResourceFact::own_memory(MemoryRange::new(
                            heap_cell(index as u64 + 1, 0),
                            MachineTerm::constant(0),
                            MachineTerm::constant(4),
                        )),
                        ResourceFact::view_memory(external_range(index as u64 + 1, 0, 4)),
                    ]
                })
                .chain(measured_kept_members()),
        );
        let (producer, checker) = kept_call_havoc_work(residual);
        produced.push((size, producer));
        checked.push((size, checker));
    }
    assert_constant_plus_log_growth("a call havoc recording kept members", &produced, 16.0);
    assert_constant_plus_log_growth(
        "checking a call havoc recording kept members",
        &checked,
        16.0,
    );
}

/// Recording the immutable flat-owner set is independent of the members
/// sharing the parameters' address block, including uncached members.
#[test]
#[ignore = "nightly: multi-size residual ownership construction"]
fn a_call_records_aliasing_kept_members_without_enumerating_them() {
    let mut produced = Vec::new();
    let mut checked = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let residual = ResourceContext::new().unchecked_with_facts(
            (0..size)
                .map(|index| ResourceFact::own_memory(external_range(index as u64 + 1, 0, 4)))
                .chain(measured_kept_members()),
        );
        let (producer, checker) = kept_call_havoc_work(residual);
        produced.push((size, producer));
        checked.push((size, checker));
    }
    assert_constant_plus_log_growth("recording aliasing kept members", &produced, 16.0);
    assert_constant_plus_log_growth("checking aliasing kept members", &checked, 16.0);
}

#[test]
fn a_call_rechecks_cached_members_after_ownership_withdrawal_or_width_change() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = external_object(KEPT_MEMBER);
    let owned = ResourceFact::own_memory(external_range(KEPT_MEMBER, 0, 1));
    let full = ResourceContext::new().unchecked_with_fact(owned.clone());
    let memory = Memory::new().store(pointer.clone(), ProgramValue::Int32(5.into()));
    memory.prepare_parameter_store_partition(&full);
    // Re-admission must classify a formerly unowned cached cell too.
    memory.prepare_parameter_store_partition(&ResourceContext::new());
    let assumptions = PureFactContext::new();
    let writes = [external_range(3_000_000, 0, 16)];
    let changed = memory.clone().store(
        pointer.clone(),
        ProgramValue::Int64(MachineTerm::int64_constant(9)),
    );
    for (before, residual, retained) in
        [
            (memory.clone(), full.clone(), true),
            (memory.clone(), ResourceContext::new(), false),
            (
                memory.clone(),
                ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
                    external_range(KEPT_MEMBER, 0, 1),
                )),
                false,
            ),
            (changed, full, false),
        ]
    {
        let kept = CallKeptOwnership::new(
            residual,
            CallKeptRanges::new(ResourceContext::new(), vec![], None),
            &assumptions,
        );
        let after = before.clone().with_call_memory_havoc(
            Variable(3_000_001),
            &writes,
            &assumptions,
            Some(&kept),
        );
        assert_eq!(after.has_known_cell_at(&pointer), retained);
        assert!(after.matches_call_memory_havoc_result(
            &before,
            &writes,
            &assumptions,
            Some(&kept)
        ));
    }
}

/// Placing a cell in a range an opened residual instance holds assumes that
/// instance's own facts, the premises that relate its fields to its cells: the
/// work is linear in the instance's body and nothing else.
#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn a_call_kept_instance_range_is_placed_in_work_linear_in_its_body() {
    const REGION: u64 = 4_000_000;
    const DATA: u64 = 4_100_000;
    const START_FIELD: u64 = 4_200_000;
    const START_LOAD: u64 = 4_300_000;
    let mut samples = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let data = |index: MachineTerm| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(external_object(DATA).offset),
                Box::new(PointerOffsetTerm::scale_int32(index, 4)),
            ),
        };
        // `data[start..start + 1]`, spelled through the instance's field.
        let range = MemoryRange::new(
            external_object(DATA),
            MachineTerm::Variable(Variable(START_FIELD)),
            MachineTerm::add(
                MachineTerm::Variable(Variable(START_FIELD)),
                MachineTerm::constant(1),
            ),
        );
        // The body facts: `region->start == start` and `size` unrelated ones.
        let premises = std::iter::once((
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(START_LOAD))),
                right: Box::new(MachineTerm::Variable(Variable(START_FIELD))),
            },
            true,
        ))
        .chain((0..size).map(|index| {
            (
                ConditionTerm::signed_less_equal(
                    MachineTerm::constant(0),
                    MachineTerm::Variable(Variable(REGION + 1 + index as u64)),
                ),
                true,
            )
        }))
        .collect();
        let kept = CallKeptRanges::new(
            ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(range)),
            premises,
            None,
        );
        let assumptions = PureFactContext::new();
        let cell = data(MachineTerm::Variable(Variable(START_LOAD)));
        let (held, work) = crate::instrumentation::measure_deterministic_work(|| {
            kept.holds_access(&cell, 4, &assumptions)
        });
        assert!(held, "the premise places the cell in the kept range");
        let (outside, _) = crate::instrumentation::measure_deterministic_work(|| {
            kept.holds_access(&external_field(REGION, 0), 4, &assumptions)
        });
        assert!(!outside, "a cell of another object is not held");
        samples.push((size, work));
    }
    eprintln!("placing a cell in an opened residual range (N, units): {samples:?}");
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        assert!(
            (*large_work as f64) <= 1.5 * (*large as f64 / *small as f64) * *small_work as f64,
            "placement work grew faster than the instance body: {samples:?}"
        );
    }
}

#[test]
fn symbolic_range_membership_ignores_unrelated_index_bounds() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(94_100));
        let index = MachineTerm::Variable(Variable(94_101));
        let end = MachineTerm::Variable(Variable(94_102));
        let range = memory_range(base.clone(), 0, end.clone());
        let pointer = base.offset_by_int32_elements(index.clone());
        let mut facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(0.into(), index.clone()),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_than(index, end.clone()), true)
            .assume_condition(
                ConditionTerm::signed_less_equal(0.into(), end.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(end.clone(), 1_073_741_823.into()),
                true,
            );
        for i in 0..size {
            let unrelated = MachineTerm::Variable(Variable(95_000 + i));
            facts = facts
                .assume_condition(
                    ConditionTerm::signed_less_equal(0.into(), unrelated.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(unrelated, end.clone()),
                    true,
                );
        }
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            let contains = |p| {
                crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
                    p, &range, &facts,
                )
            };
            (
                contains(&pointer),
                contains(&base.offset_by_int32_elements(MachineTerm::Variable(Variable(99_999)))),
            )
        });
        assert_eq!(verdicts, (true, false));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "symbolic membership scanned unrelated bounds: {samples:?}"
    );
}

/// [`symbolic_range_membership_ignores_unrelated_index_bounds`] for a range
/// with unsigned 64-bit bounds. The access at index `i` is placed in
/// `base[0..end]` by deciding `i < end` and the extent limit on `end`; the
/// bounds other indices have against the same `end` are edges below `end`,
/// which an upward order walk through it does not read.
#[test]
fn wide_range_membership_ignores_unrelated_index_bounds() {
    let mut samples = Vec::new();
    for size in [64, 128, 256, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(96_100));
        let index = MachineTerm::Variable(Variable(96_101));
        let end = MachineTerm::Variable(Variable(96_102));
        let range = MemoryRange::new_wide(
            base.clone(),
            MachineTerm::uint64_constant(0),
            end.clone(),
            4,
        );
        let at = |index: MachineTerm| base.offset_by_typed_elements(index, 4, true, true);
        let mut facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_than(index.clone(), end.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    end.clone(),
                    MachineTerm::uint64_constant(i64::MAX as u64 / 4),
                ),
                true,
            );
        for i in 0..size {
            let unrelated = MachineTerm::Variable(Variable(97_000 + i));
            facts = facts.assume_condition(
                ConditionTerm::uint64_less_than(unrelated, end.clone()),
                true,
            );
        }
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            let contains = |p| {
                crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
                    p, &range, &facts,
                )
            };
            (
                contains(&at(index.clone())),
                contains(&at(MachineTerm::Variable(Variable(99_998)))),
            )
        });
        assert_eq!(verdicts, (true, false));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "wide membership scanned unrelated bounds: {samples:?}"
    );
}

/// A kept range whose base is not one of the access's own spellings is
/// related to it by a proved base equality, asked once per fact set: every
/// walk across the call asks the same question about the same kept range,
/// and the repeats cost a keyed lookup, however many facts the proof holds.
#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn a_kept_range_base_equality_is_proved_once_per_fact_set() {
    const KEPT: u64 = 6_000_000;
    const ACCESS: u64 = 6_100_000;
    let mut repeats = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let mut assumptions = PureFactContext::new();
        for index in 0..size as u64 {
            assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(
                    external_object(2 * index + 1),
                    external_object(2 * index + 2),
                ),
                true,
            ));
        }
        let kept = CallKeptRanges::new(
            ResourceContext::new()
                .unchecked_with_facts([ResourceFact::own_memory(external_range(KEPT, 0, 4))]),
            Vec::new(),
            None,
        );
        let access = external_field(ACCESS, 8);
        assert!(
            !kept.holds_access(&access, 4, &assumptions),
            "nothing relates the access's object to the kept one"
        );
        let (held, work) = crate::instrumentation::measure_deterministic_work(|| {
            kept.holds_access(&access, 4, &assumptions)
        });
        assert!(!held);
        repeats.push((size, work));
    }
    assert_constant_plus_log_growth("asking a kept range's base equality again", &repeats, 16.0);
}

/// A cell of an object the queried range is spelled through an alias of is
/// inside the range, so it is never separate from it. `arena + 16` against
/// `x[4..5)` of four-byte elements under `arena == x` is decided from the
/// constant displacement and the one alias fact, before any separation fact
/// is visited: a call havoc lending an arena state asks this about every
/// arena field on every walk across it.
#[test]
fn an_aliased_field_inside_a_range_is_not_searched_for_a_separation() {
    const OBJECT: u64 = 5_000_000;
    const ALIAS: u64 = 5_100_000;
    let mut samples = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let mut assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(external_object(OBJECT), external_object(ALIAS)),
            true,
        ));
        for index in 0..size as u64 {
            assumptions = assumptions.assume_proposition(Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(external_range(2 * index + 1, 0, 4))),
                right: Box::new(Resource::Memory(external_range(2 * index + 2, 0, 4))),
            });
        }
        let ranges = [external_range(ALIAS, 4, 5)];
        let pointer = external_field(OBJECT, 16);
        let (disjoint, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.ranges_proven_disjoint_from_pointer(&ranges, &pointer)
        });
        assert!(
            !disjoint,
            "a field inside the range is not separate from it"
        );
        samples.push((size, work));
        let outside = external_field(OBJECT, 20);
        assert!(
            !assumptions.pointer_overlaps_range_after_path_equality(&outside, &ranges[0]),
            "the next field lies past the range"
        );
    }
    assert_constant_plus_log_growth("an aliased field inside a queried range", &samples, 16.0);
}

/// A fact context's stated propositions are a persistent set: a clone shares
/// it, and extending the clone leaves the original's set untouched.
#[test]
fn extending_a_cloned_context_leaves_the_original_propositions() {
    let separation = |index: u64| Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(external_range(2 * index + 1, 0, 4))),
        right: Box::new(Resource::Memory(external_range(2 * index + 2, 0, 4))),
    };
    let original = (0..64).fold(PureFactContext::new(), |context, index| {
        context.assume_proposition(separation(index))
    });
    let clone = original.clone();
    assert!(clone.prop_facts.ptr_eq(&original.prop_facts));
    let extended = clone.assume_proposition(separation(64));
    assert_eq!(original.prop_facts.len(), 64);
    assert_eq!(extended.prop_facts.len(), 65);
    assert!(!original.prop_facts.contains(&separation(64)));
}

/// The wide order chain (`design/typed-indices.md`, stage 2, step 1):
/// `x < n` and `n <= 4` as `uint64` facts beside `N` other indices below the same `n`. Deciding
/// `x < 4` walks up from `x` and must not read the bounds that only share
/// `n`, so its work is the same at every size.
#[test]
fn wide_order_walk_ignores_uint64_bounds_of_other_indices() {
    let variable = |id: u64| MachineTerm::Variable(Variable(97_600 + id));
    let (x, n) = (variable(0), variable(1));
    let four = MachineTerm::uint64_constant(4);
    let bounded = |facts: PureFactContext, index: &MachineTerm| {
        facts.assume_condition(
            ConditionTerm::uint64_less_than(index.clone(), n.clone()),
            true,
        )
    };
    let mut work = Vec::new();
    for size in [64u64, 128, 256, 512] {
        let facts = (0..size).fold(
            bounded(
                PureFactContext::new().assume_condition(
                    ConditionTerm::uint64_less_equal(n.clone(), four.clone()),
                    true,
                ),
                &x,
            ),
            |facts, index| bounded(facts, &variable(10 + index)),
        );
        let (answer, cost) = crate::instrumentation::measure_deterministic_work(|| {
            facts.decide(&ConditionTerm::uint64_less_than(x.clone(), four.clone()))
        });
        assert_eq!(answer, Some(true), "the wide chain at {size}");
        work.push((size, cost));
    }
    assert!(
        work.iter().all(|(_, cost)| *cost == work[0].1),
        "the wide order walk visited unrelated bounds: {work:?}"
    );
}

/// A store the facts cannot place forgets every element of a fully written
/// automatic array, and records their bytes initialized as it goes: one run
/// for the whole array, built in work N·log N in the array, and a later
/// covering query is one lookup whatever the array's size.
#[test]
fn an_unplaced_store_records_a_local_array_as_one_run() {
    let index = MachineTerm::Variable(Variable(7_001));
    let mut samples = Vec::new();
    for size in SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let block = "local:scaling-array";
        let written = (0..size).fold(
            Memory::new().with_block(block, u32::try_from(4 * size).unwrap()),
            |memory, element| memory.store(scaling_cell(block, element), scaling_value(element)),
        );
        let unplaced = Pointer {
            block: PointerBlock::from(block),
            offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
        };
        let (forgotten, work) = crate::instrumentation::measure_deterministic_work(|| {
            written.without_possible_aliasing_cells(&unplaced, 4, &PureFactContext::new())
        });
        assert_eq!(
            forgotten.cells.len(),
            0,
            "the unplaced store keeps no element"
        );
        assert_eq!(
            forgotten.heap.initialized.as_map().len(),
            1,
            "{size} forgotten elements are one initialized run"
        );
        let (covered, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            forgotten.has_initialized_bytes_at(&scaling_cell(block, size - 1), 4)
        });
        assert!(covered);
        assert!(
            query_work <= 2,
            "a covering query charged {query_work} units"
        );
        assert!(!forgotten.has_initialized_bytes_at(&scaling_cell(block, size), 4));
        samples.push((size, work));
    }
    eprintln!("unplaced-store forget work (N, units): {samples:?}");
    for pair in samples.windows(2) {
        let [(small, small_work), (large, large_work)] = pair else {
            unreachable!()
        };
        let allowed = (*large as f64 * log2(*large)) / (*small as f64 * log2(*small)) * 1.25;
        let ratio = *large_work as f64 / *small_work as f64;
        assert!(
            ratio <= allowed,
            "forgetting a local array grew by {ratio:.2} from {small} to {large} elements, \
             above the N·log N ratio {allowed:.2}: {samples:?}"
        );
    }
}

#[test]
fn wide_shifted_suffix_coverage_ignores_unrelated_bounds() {
    let mut samples = Vec::new();
    for size in [0, 64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(983_300));
        let n = MachineTerm::Variable(Variable(983_301));
        let count = MachineTerm::Variable(Variable(983_302));
        let available =
            MemoryRange::new_wide(base.clone(), MachineTerm::uint64_constant(0), n.clone(), 4);
        let required = MemoryRange::new_wide(
            base.offset_by_typed_elements(
                MachineTerm::uint64_subtract(n.clone(), count.clone()),
                4,
                true,
                true,
            ),
            MachineTerm::uint64_constant(0),
            count.clone(),
            4,
        );
        let mut facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    n.clone(),
                    MachineTerm::uint64_constant(i64::MAX as u64 / 4),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(count.clone(), n.clone()),
                true,
            );
        let offset_suffix = MemoryRange::new_wide(
            base.offset_by_typed_elements(count.clone(), 4, true, true),
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_subtract(n.clone(), count),
            4,
        );
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::uint64_less_equal(
                    MachineTerm::Variable(Variable(984_000 + i)),
                    n.clone(),
                ),
                true,
            );
        }
        let (covered, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::primitives::wide_memory_range_covers(&available, &required, &facts)
                && crate::kernel::primitives::wide_memory_range_covers(
                    &available,
                    &offset_suffix,
                    &facts,
                )
        });
        assert!(covered);
        samples.push(work);
    }
    // Every unrelated bound shares `n`, so the difference graph's bounded
    // propagation (`EDGE_LIMIT`) follows a fixed number of their edges once
    // there are more of them than the limit: the work is constant from then
    // on, and above no unrelated bounds by at most a fixed multiple of the
    // limit (124 units at a limit of 32 when this was written).
    let limit = crate::kernel::difference_graph::EDGE_LIMIT;
    assert!(
        samples[1..].windows(2).all(|pair| pair[0] == pair[1])
            && samples[1] <= samples[0] + 8 * limit,
        "suffix coverage scanned unrelated bounds: {samples:?}"
    );
}

// Observer transport must use the exact equality index, even with many
// unrelated facts and a later state containing an unrelated write.
#[test]
fn wide_range_observer_transport_ignores_unrelated_equalities() {
    for same_value_class in [false, true] {
        let mut samples = Vec::new();
        for size in [0, 64, 128, 512] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = scaling_cell("global:wide-observer", 0);
            let memory = Memory::new().store(
                pointer.clone(),
                ProgramValue::UInt64(MachineTerm::uint64_constant(3)),
            );
            let load = |memory| {
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(memory),
                    Box::new(pointer.clone()),
                    LoadKind::Bits64,
                )
            };
            let before = load(memory.clone());
            let after = load(memory.store(
                scaling_cell("global:beside-wide-observer", 0),
                ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
            ));
            let observer = MachineTerm::Variable(Variable(985_002));
            let mut facts = PureFactContext::new()
                .assume_condition(ConditionTerm::uint64_equal(observer.clone(), before), true);
            // Structural read-over-write matching also files observer == 3.
            // Keep unrelated values out of that class. Separately grow aliases
            // of 3 from a fixed one-alias baseline, so both sides measure the
            // same union-find root shape rather than its first class merge.
            if same_value_class {
                facts = facts.assume_condition(
                    ConditionTerm::uint64_equal(
                        MachineTerm::Variable(Variable(985_003)),
                        MachineTerm::uint64_constant(3),
                    ),
                    true,
                );
            }
            for index in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::uint64_equal(
                        MachineTerm::Variable(Variable(986_000 + index)),
                        MachineTerm::uint64_constant(if same_value_class {
                            3
                        } else {
                            1000 + index
                        }),
                    ),
                    true,
                );
            }
            // Extending a context discards its root-lookup cache. Give the
            // zero-extension sample the same cold cache as the larger ones.
            let facts = facts.clone();
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.uint64_values_equal_for_range_resolution(&observer, &after)
            });
            assert!(equal);
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "observer transport scanned equalities (same value class: {same_value_class}): {samples:?}"
        );
    }
}

/// Counts the bytes a value feeds its hasher.
#[derive(Default)]
struct CountingHasher {
    bytes: usize,
}

impl std::hash::Hasher for CountingHasher {
    fn finish(&self) -> u64 {
        self.bytes as u64
    }

    fn write(&mut self, bytes: &[u8]) {
        self.bytes += bytes.len();
    }
}

/// Every call publishes an effect summary naming the memory before and after
/// it, and facts are hashed whenever they are inserted or looked up. An atomic
/// proposition used to hash its debug text, which printed every state it
/// names, so a fact about a memory cost the size of that memory and each call
/// in a long function paid more than the last (512 calls: 7.3 s, 2.1 times
/// the linear cost). The hasher is uncharged, so no work budget saw it. A
/// proposition now hashes a state by its cached content hash: the bytes it
/// feeds a hasher do not depend on how much memory the state holds.
#[test]
fn hashing_a_memory_fact_is_constant_in_the_memory_size() {
    use std::hash::Hash;
    let mut samples = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let after = memory_with_unrelated_allocations(size);
        let fact = Proposition::MemoryEffectSummary {
            before: Memory::new(),
            after,
            mutable_ranges: Vec::new(),
        };
        let mut hasher = CountingHasher::default();
        fact.hash(&mut hasher);
        samples.push((size, hasher.bytes));
    }
    let (_, smallest) = samples[0];
    assert!(
        samples.iter().all(|(_, bytes)| *bytes == smallest),
        "hashing a memory fact fed its hasher bytes in proportion to the memory: {samples:?}"
    );
}

/// Stores to a sequence of separately owned parameter fields must not revisit
/// cached fields of earlier objects. Check both scalar and pointer contents;
/// the latter reproduces the linked-node shape from the bug report.
#[test]
fn sequential_owned_parameter_stores_ignore_earlier_cached_fields() {
    let mut samples = Vec::new();
    for pointer_values in [false, true] {
        for count in [4, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let objects: Vec<_> = (0..count)
                .map(|index| Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(
                        MachineTerm::Variable(Variable(980_000 + index as u64)),
                        4,
                    ),
                })
                .collect();
            let composition = objects
                .iter()
                .fold(ResourceContext::new(), |resources, base| {
                    resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                        base.clone(),
                        0u32.into(),
                        4u32.into(),
                    )))
                });
            let assumptions = PureFactContext::new()
                .assume_proposition(Proposition::ResourceComposition(composition));
            let mut memory = Memory::new();
            let mut largest = 0;
            for (index, object) in objects.iter().enumerate() {
                let value = if pointer_values {
                    ProgramValue::pointer(objects[(index + 1) % count].clone())
                } else {
                    scaling_value(index)
                };
                let width = value.byte_width();
                let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
                    memory.without_possible_aliasing_cells(object, width, &assumptions)
                });
                largest = largest.max(work);
                memory = next.store(object.clone(), value);
            }
            for (index, object) in objects.iter().enumerate() {
                let value = if pointer_values {
                    ProgramValue::pointer(objects[(index + 1) % count].clone())
                } else {
                    scaling_value(index)
                };
                assert_eq!(memory.known_value(object), Some(value));
            }
            samples.push((pointer_values, count, largest));
        }
    }
    assert!(
        samples.iter().all(|(_, _, work)| *work <= 100),
        "a field store visited unrelated cached objects: {samples:?}"
    );
}

/// A store through a pointer value never visits the slot of a local whose
/// address is never taken: no pointer value designates one
/// (`never_address_taken_local_versus_pointer_value`). Each slot keeps its
/// value, and the store's work is the same beside 16, 64 or 256 of them.
#[test]
fn a_symbolic_store_skips_locals_whose_address_is_never_taken() {
    let mut samples = Vec::new();
    for size in [16usize, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..size).map(|index| format!("hidden{index}")).collect(),
        );
        let slot = |index: usize| scaling_cell(&format!("local:hidden{index}"), 0);
        let mut memory = Memory::new();
        for index in 0..size {
            memory = memory
                .with_block(slot(index).block.clone(), 4)
                .store(slot(index), scaling_value(index));
        }
        let written = Pointer::symbolic(Variable(98_500));
        // The first store catches the reachable-cell index up to this
        // memory; the measured one pays only the change since.
        let memory = memory.without_possible_aliasing_cells(&written, 4, &PureFactContext::new());
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.without_possible_aliasing_cells(&written, 4, &PureFactContext::new())
        });
        assert!(
            (0..size).all(|index| after.has_known_cell_at(&slot(index))),
            "size {size}: a store through a pointer value dropped a local's slot"
        );
        crate::kernel::clear_never_address_taken_locals();
        samples.push((size, work));
    }
    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 4),
        "a store through a pointer value visits locals no pointer reaches: {samples:?}"
    );
}

/// Catches a condition-fact query that falls back to every fact of its kind
/// with a non-atom side. Facts `v + 1 < w` about unrelated variables have a
/// sum side, so they are not filed under a key a query spells; a query that
/// misses its keys reads only the facts filed under its own variables and
/// their recorded-equality classes, whatever the number of unrelated facts.
#[test]
fn open_sided_condition_queries_read_only_their_variables_facts() {
    let variable = |id: u64| MachineTerm::Variable(Variable(96_000 + id));
    let successor = |term: MachineTerm| MachineTerm::add(term, MachineTerm::constant(1));
    let (a, x, y) = (variable(0), variable(1), variable(2));
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let mut facts = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(a.clone(), x.clone()), true)
            .assume_condition(
                ConditionTerm::signed_less_than(successor(a.clone()), y.clone()),
                true,
            );
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::signed_less_than(
                    successor(variable(100 + 2 * index)),
                    variable(101 + 2 * index),
                ),
                true,
            );
        }
        let visits = |condition: ConditionTerm, expected: bool| {
            PureFactContext::reset_condition_fact_visits();
            assert_eq!(facts.has_condition_fact(condition, true), expected);
            PureFactContext::condition_fact_visits()
        };
        let through_class = visits(
            ConditionTerm::signed_less_than(successor(x.clone()), y.clone()),
            true,
        );
        let miss = visits(
            ConditionTerm::signed_less_than(successor(y.clone()), x.clone()),
            false,
        );
        samples.push((size, through_class, miss));
    }
    assert!(
        samples
            .iter()
            .all(|(_, hit, miss)| (*hit, *miss) == (samples[0].1, samples[0].2)),
        "{samples:?}"
    );
}

/// Literal discovery and its memory caller must not rediscover equality paths.
#[test]
fn direct_literal_checks_do_not_walk_related_equality_classes() {
    for shape in ["chain", "star", "unrelated", "unpinned", "folded"] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let var = |i| MachineTerm::Variable(Variable(990_000 + i));
            let mut facts = PureFactContext::new();
            for i in 1..=size {
                let (a, b) = match shape {
                    "chain" => (var(i - 1), var(i)),
                    "unrelated" => (var(2 * i), var(2 * i + 1)),
                    _ => (var(0), var(i)),
                };
                facts = facts.assume_condition(ConditionTerm::equal(a, b), true);
            }
            if shape != "unpinned" {
                let endpoint = if shape == "unrelated" {
                    var(0)
                } else {
                    var(size)
                };
                facts = facts.assume_condition(ConditionTerm::equal(endpoint, 7u32.into()), true);
            }
            let query = if shape == "folded" {
                MachineTerm::add(var(0), 1u32.into())
            } else {
                var(0)
            };
            let expected = if shape == "unrelated" { Some(7) } else { None };
            let pointer = |index| Pointer {
                block: Pointer::symbolic(Variable(995_000)).block,
                offset: PointerOffsetTerm::scale_int32(index, 4),
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert_eq!(
                        facts.bitvector_constant_from_direct_equalities(&query),
                        expected
                    );
                    let _ = facts.decide_bitvector_equality_shallow(&query, &9u32.into());
                    let _ = crate::kernel::reasoning::memory_resolution::pointers_proven_distinct_for_memory_resolution(
                        &pointer(query.clone()), &pointer(9u32.into()), &facts);
                }
            });
            let explicit =
                facts.assume_condition(ConditionTerm::equal(query.clone(), 7u32.into()), true);
            // A folded term was already pinned to 8; do not use a contradictory
            // branch as evidence for the successful literal path.
            if shape != "folded" {
                let (_, hit_work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..4 {
                        assert_eq!(
                            explicit.bitvector_constant_from_direct_equalities(&query),
                            Some(7)
                        );
                        assert_eq!(
                            explicit.decide_bitvector_equality_shallow(&query, &9u32.into()),
                            Some(false)
                        );
                        assert!(crate::kernel::reasoning::memory_resolution::pointers_proven_distinct_for_memory_resolution(
                            &pointer(query.clone()), &pointer(9u32.into()), &explicit));
                    }
                });
                assert!(hit_work <= 300, "{shape} hit grew at {size}: {hit_work}");
            }
            samples.push((size, work));
        }
        assert!(
            samples.iter().all(|(_, work)| *work <= 300),
            "{shape}: {samples:?}"
        );
        eprintln!("direct literal checking {shape}: {samples:?}");
    }
}

#[test]
fn store_preservation_ignores_unrelated_owned_members() {
    for explicit_owner in [false, true] {
        let mut samples = Vec::new();
        for size in [4u64, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let object = |i| Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(997_000 + i)),
            };
            let own =
                |i| ResourceFact::own_memory(MemoryRange::new(object(i), 0u32.into(), 2u32.into()));
            let mut facts = PureFactContext::new();
            let mut owner = ResourceContext::new().unchecked_with_fact(own(0));
            for i in 1..=size {
                let resources = ResourceContext::new()
                    .unchecked_with_fact(own(2 * i + 10))
                    .unchecked_with_fact(own(2 * i + 11));
                facts = facts.assume_proposition(Proposition::ResourceComposition(resources));
                owner = owner.unchecked_with_fact(own(i + 1000));
            }
            facts = facts.assume_proposition(Proposition::ResourceComposition(owner.clone()));
            if explicit_owner {
                facts = facts.with_store_owner(Some(owner));
            }
            let write = object(0).offset_by_bytes(4);
            let read = object(1).offset_by_bytes(4);
            let kept = object(1001).offset_by_bytes(4);
            let memory = Memory::new()
                .store(read.clone(), scaling_value(9))
                .store(kept.clone(), scaling_value(10))
                .store(write.clone(), scaling_value(11));
            let mut measured = Vec::new();
            for _ in 0..2 {
                let ((after, events), work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        crate::instrumentation::collect(|| {
                            memory.without_possible_aliasing_cells(&write, 4, &facts)
                        })
                    });
                assert!(!after.has_known_cell_at(&read));
                assert!(!after.has_known_cell_at(&write));
                assert!(after.has_known_cell_at(&kept));
                assert!(
                    events.iter().all(|event| !matches!(event,
                        crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                            if name == "composition-owned store separation"
                    )),
                    "a store miss retried the general composition search at size {size}"
                );
                measured.push(work);
            }
            samples.push((size, measured));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "unrelated ownership changed cold or warm store work (explicit_owner={explicit_owner}): {samples:?}"
        );
        eprintln!("store preservation explicit_owner={explicit_owner}: {samples:?}");
    }
}

#[test]
fn store_distinctness_does_not_search_same_block_range_candidates() {
    let index = |i| MachineTerm::Variable(Variable(998_000 + i));
    let pointer = |i| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(index(i), 4),
    };
    let mut samples = Vec::new();
    for size in [4u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_proposition(Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(MemoryRange::new(
                    pointer(2 * i + 10),
                    0u32.into(),
                    1u32.into(),
                ))),
                right: Box::new(Resource::Memory(MemoryRange::new(
                    pointer(2 * i + 11),
                    0u32.into(),
                    1u32.into(),
                ))),
            });
        }
        let memory = Memory::new().store(pointer(1), scaling_value(9));
        let mut measured = Vec::new();
        for _ in 0..2 {
            let ((after, events), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    crate::instrumentation::collect(|| {
                        memory.without_possible_aliasing_cells(&pointer(0), 4, &facts)
                    })
                });
            assert!(!after.has_known_cell_at(&pointer(1)));
            assert!(events.iter().all(|event| !matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name.starts_with("explicit range:") || name.starts_with("general distinctness:")
            )), "a store entered general distinctness or range search at size {size}");
            measured.push(work);
        }
        let distinct = facts.assume_condition(ConditionTerm::equal(index(0), index(1)), false);
        assert!(
            memory
                .without_possible_aliasing_cells(&pointer(0), 4, &distinct)
                .has_known_cell_at(&pointer(1)),
            "written index disequality keeps a narrow cell"
        );
        assert!(
            !memory
                .without_possible_aliasing_cells(&pointer(0), 8, &distinct)
                .has_known_cell_at(&pointer(1)),
            "index disequality does not separate an overlapping wide store"
        );
        samples.push((size, measured));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
        "same-block range candidates changed store miss work: {samples:?}"
    );
    eprintln!("store distinctness misses: {samples:?}");
}

/// A store keeps a cached cell of the same array beside a 64-bit scaled index
/// on one exact comparison fact in the indices' own format (`size_t` or
/// `long`), the second key shape of `pointers_directly_distinct_for_store`.
/// Its lookups are keyed by the two indices, so growing unrelated facts, and
/// facts about other cells of the same array, leaves a hit and a miss at
/// fixed work; a store over many same-array cells pays one keyed check per
/// cell. A mixed 32/64-bit or mixed-signedness pair has no key.
#[test]
fn wide_store_index_lookup_ignores_unrelated_facts_and_same_array_cells() {
    for unsigned in [true, false] {
        let format = if unsigned {
            MachineIntegerType::UInt64
        } else {
            MachineIntegerType::Int64
        };
        let index = |i: u64| MachineTerm::Variable(Variable(999_100 + i));
        let pointer = |i: u64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int64(index(i), 4, unsigned),
        };
        let differ = |i: u64, j: u64| {
            ConditionTerm::machine_compare(format, CompareRelation::Equal, index(i), index(j))
        };
        let mut lookups = Vec::new();
        let mut stores = Vec::new();
        for size in [4u64, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut facts = PureFactContext::new();
            let mut memory = Memory::new();
            for k in 0..size {
                // Unrelated index facts, and the written index against
                // other cells of the same array.
                facts = facts
                    .assume_condition(differ(2 * k + 1000, 2 * k + 1001), false)
                    .assume_condition(
                        ConditionTerm::machine_compare(
                            format,
                            CompareRelation::LessThan,
                            index(3 * k + 5000),
                            index(3 * k + 5001),
                        ),
                        true,
                    )
                    .assume_condition(differ(0, k + 10), false);
                memory = memory.store(pointer(k + 10), scaling_value(k as usize));
            }
            let hit = facts.clone().assume_condition(differ(0, 1), false);
            let below = facts.clone().assume_condition(
                ConditionTerm::machine_compare(
                    format,
                    CompareRelation::LessThan,
                    index(1),
                    index(0),
                ),
                true,
            );
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(
                        crate::kernel::reasoning::pointers_directly_distinct_for_store(
                            &pointer(1),
                            &pointer(0),
                            &hit
                        )
                    );
                    assert!(
                        crate::kernel::reasoning::pointers_directly_distinct_for_store(
                            &pointer(0),
                            &pointer(1),
                            &hit
                        )
                    );
                    assert!(
                        crate::kernel::reasoning::pointers_directly_distinct_for_store(
                            &pointer(1),
                            &pointer(0),
                            &below
                        )
                    );
                    assert!(
                        !crate::kernel::reasoning::pointers_directly_distinct_for_store(
                            &pointer(1),
                            &pointer(0),
                            &facts
                        )
                    );
                }
            });
            lookups.push((size, work));
            // Every same-array cell is kept by its own stated fact.
            let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.without_possible_aliasing_cells(&pointer(0), 4, &facts)
            });
            assert!(
                (0..size).all(|k| after.has_known_cell_at(&pointer(k + 10))),
                "a stated wide index disequality kept every cell at {size}"
            );
            stores.push((size, work));
            // The other signedness, and a 32-bit index, have no key.
            let other = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int64(index(1), 4, !unsigned),
            };
            let narrow = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(index(1), 4),
            };
            for declined in [other, narrow] {
                assert!(
                    !crate::kernel::reasoning::pointers_directly_distinct_for_store(
                        &declined,
                        &pointer(0),
                        &hit
                    )
                );
            }
        }
        assert!(
            lookups.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "unsigned={unsigned}: wide index lookups grew with facts: {lookups:?}"
        );
        // Four times the cells: one keyed check per cell, with persistent
        // map factors.
        assert!(
            stores.windows(2).all(|pair| pair[1].1 <= pair[0].1 * 5),
            "unsigned={unsigned}: store work grew faster than its cells: {stores:?}"
        );
        eprintln!(
            "wide store index lookups (unsigned={unsigned}): {lookups:?}; stores: {stores:?}"
        );
    }
}

#[test]
fn store_ownership_selection_bounds_same_base_candidates() {
    for explicit_owner in [false, true] {
        for crowded_read in [false, true] {
            for miss in [false, true] {
                let mut samples = Vec::new();
                for size in [4u64, 16, 64] {
                    let _session = crate::kernel::VerificationSession::enter();
                    let object = |i| Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(999_100 + i)),
                    };
                    let own = |base, start: u32| {
                        ResourceFact::own_memory(MemoryRange::new(
                            object(base),
                            start.into(),
                            (start + 1).into(),
                        ))
                    };
                    let crowded = u64::from(crowded_read);
                    let mut owner = ResourceContext::new().unchecked_with_fact(own(1 - crowded, 0));
                    for i in 0..size {
                        owner = owner.unchecked_with_fact(own(crowded, (2 * i) as u32));
                    }
                    let mut facts = PureFactContext::new()
                        .assume_proposition(Proposition::ResourceComposition(owner.clone()));
                    if explicit_owner {
                        facts = facts.with_store_owner(Some(owner));
                    }
                    let offset = if miss { 4 } else { 0 };
                    let write = object(0).offset_by_bytes(if crowded_read { 0 } else { offset });
                    let read = object(1).offset_by_bytes(if crowded_read { offset } else { 0 });
                    // Fixed cache and fixed delta: only the ownership bucket grows.
                    let memory = Memory::new().store(read.clone(), scaling_value(9));
                    let mut work = Vec::new();
                    for _ in 0..3 {
                        let (after, units) =
                            crate::instrumentation::measure_deterministic_work(|| {
                                memory.without_possible_aliasing_cells(&write, 4, &facts)
                            });
                        assert!(
                            !after.has_known_cell_at(&read),
                            "crowded ownership declines implicit preservation"
                        );
                        work.push(units);
                    }
                    samples.push((size, work));
                }
                assert!(
                    samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
                    "ownership members explicit={explicit_owner} read={crowded_read} miss={miss}: {samples:?}"
                );
            }
        }
    }
}

#[test]
fn store_ownership_selection_bounds_same_base_compositions() {
    for miss in [false, true] {
        let mut samples = Vec::new();
        for size in [4u64, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let object = |i| Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(999_500 + i)),
            };
            let own = |base, end: u32| {
                ResourceFact::own_memory(MemoryRange::new(object(base), 0u32.into(), end.into()))
            };
            let mut facts =
                PureFactContext::new().assume_proposition(Proposition::ResourceComposition(
                    ResourceContext::new().unchecked_with_fact(own(1, 1)),
                ));
            for i in 0..size {
                let owner = ResourceContext::new()
                    .unchecked_with_fact(own(0, i as u32 + 1))
                    .unchecked_with_fact(own(10 + i, 1));
                facts = facts.assume_proposition(Proposition::ResourceComposition(owner));
            }
            let write = object(0);
            let read = object(if miss { 9 } else { 9 + size });
            let memory = Memory::new().store(read, scaling_value(9));
            let mut work = Vec::new();
            for _ in 0..3 {
                let (_, units) = crate::instrumentation::measure_deterministic_work(|| {
                    memory.without_possible_aliasing_cells(&write, 4, &facts)
                });
                work.push(units);
            }
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "ownership compositions miss={miss}: {samples:?}"
        );
        eprintln!("ownership compositions miss={miss}: {samples:?}");
    }
}

#[test]
fn store_byte_gap_bounds_recorded_order_walks() {
    for hit in [false, true] {
        let mut samples = Vec::new();
        for size in [4u64, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let index = |i| MachineTerm::Variable(Variable(999_800 + i));
            let pointer = |i| Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(index(i), 4),
            };
            let mut facts = PureFactContext::new();
            for i in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_than(index(i), index(i + 1)),
                    true,
                );
            }
            let read = pointer(if hit { size } else { size + 1 });
            let memory = Memory::new().store(read, scaling_value(9));
            let mut work = Vec::new();
            for _ in 0..3 {
                let (_, units) = crate::instrumentation::measure_deterministic_work(|| {
                    memory.without_possible_aliasing_cells(&pointer(0), 8, &facts)
                });
                work.push(units);
            }
            samples.push((size, work));
        }
        eprintln!("byte-gap order hit={hit}: {samples:?}");
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "{samples:?}"
        );
    }
}

#[test]
fn pointer_frame_through_seeded_cells_ignores_run_length() {
    let mut samples = Vec::new();
    for count in [1u32, 128, 65_536] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(128),
        };
        let source = crate::kernel::intern_memory(Memory::new());
        // The seed reads the original source, not its immediate parent.
        let seeded = Memory::new()
            .store(
                field.offset_by_bytes(count * 8 + 16),
                ProgramValue::Int32(7u32.into()),
            )
            .with_seeded_cells(
                field.clone(),
                8,
                ProgramType::Int32Pointer,
                0,
                count,
                source.clone(),
            );
        let context = PureFactContext::new();
        // Prepare a partial write: discard the cached whole pointer, but
        // do not perform the write yet. This records cache-only forgetting.
        let seed_state = crate::kernel::intern_memory(seeded.clone());
        let seeded_read = Pointer::loaded_value(&seed_state, &field);
        let forgotten = seeded.without_possible_aliasing_cells(&field, 4, &context);
        assert!(!forgotten.has_known_cell_at(&field));
        let before = Pointer::loaded_value(&source, &field);
        let after_memory = crate::kernel::intern_memory(forgotten.clone());
        let after = Pointer::loaded_value(&after_memory, &field);
        let mut work = Vec::new();
        for _ in 0..3 {
            let (equal, units) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                    &before,
                    &seeded_read,
                    &context,
                ) && crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                    &seeded_read,
                    &after,
                    &context,
                )
            });
            assert!(
                equal,
                "a seeded complete pointer still names its original read"
            );
            work.push(units);
        }
        samples.push((count, work));
        for address in [field.clone(), field.offset_by_bytes(4)] {
            let changed = crate::kernel::intern_memory(
                forgotten
                    .clone()
                    .store(address, ProgramValue::Int32(9u32.into())),
            );
            assert!(
                !crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                    &before,
                    &Pointer::loaded_value(&changed, &field),
                    &context,
                ),
                "overwriting either pointer half invalidates the frame"
            );
        }
        let changed = crate::kernel::intern_memory(forgotten.store(
            field.clone(),
            ProgramValue::typed_pointer(
                Pointer::symbolic(Variable(998_902)),
                ProgramType::Int32Pointer,
            ),
        ));
        assert!(
            !crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                &before,
                &Pointer::loaded_value(&changed, &field),
                &context,
            )
        );
        assert!(
            !crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                &before,
                &after.offset_by_bytes(4),
                &context,
            )
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
        "{samples:?}"
    );
}

/// N stores and N explicit frame queries; retain every proved
/// equality and keep all caches live within the sequence. Distinct symbolic
/// addresses require the supplied full-byte separation, rather than letting
/// a fact-free distinct-block rule erase the interesting history.
fn repeated_pointer_frame_work(compare_to_entry: bool, compose: bool) -> Vec<(u32, usize)> {
    let mut samples = Vec::new();
    for size in [4u32, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(998_910));
        let write = Pointer::symbolic(Variable(998_911));
        let initial = crate::kernel::intern_memory(Memory::new());
        let original = PointerValue::new(
            Pointer::loaded_value(&initial, &field),
            ProgramType::Int32Pointer,
        );
        let mut facts = PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                field.clone(),
                0u32.into(),
                8u32.into(),
                1,
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                write.clone(),
                0u32.into(),
                4u32.into(),
                1,
            ))),
        });
        let mut memory = initial.memory().clone();
        let mut previous = original.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                memory = memory
                    .clone()
                    .store(write.clone(), ProgramValue::Int32(index.into()));
                let retained_state = crate::kernel::intern_memory_ref(&memory);
                let current = PointerValue::new(
                    Pointer::loaded_value(&retained_state, &field),
                    ProgramType::Int32Pointer,
                );
                let reference = if compare_to_entry {
                    &original
                } else {
                    &previous
                };
                let source = Proposition::ConditionIs(
                    ConditionTerm::pointer_value_equal(reference.clone(), reference.clone()),
                    true,
                );
                let target = Proposition::ConditionIs(
                    ConditionTerm::pointer_value_equal(current.clone(), reference.clone()),
                    true,
                );
                let proved = crate::kernel::api::program_condition_fact_target_reaches_in_context(
                    &source, &target, &facts,
                );
                if !compare_to_entry || index == 0 {
                    assert!(proved, "adjacent control: query {index} of {size}");
                }
                // Keep every proved equality; a declined history query adds nothing.
                if proved {
                    facts = facts.clone().assume_proposition(target);
                }
                if compose {
                    let composed = Proposition::ConditionIs(
                        ConditionTerm::pointer_value_equal(current.clone(), original.clone()),
                        true,
                    );
                    assert!(
                        crate::kernel::api::program_condition_fact_target_reaches_in_context(
                            &source, &composed, &facts,
                        ),
                        "composition at {index} of {size}"
                    );
                    facts = facts.clone().assume_proposition(composed);
                }
                previous = current;
            }
        });
        samples.push((size, work));
    }
    samples
}

#[test]
fn adjacent_pointer_frame_checks_have_near_linear_total_work() {
    let samples = repeated_pointer_frame_work(false, false);
    eprintln!("adjacent-state pointer checks: {samples:?}");
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 3, "adjacent control: {samples:?}");
    }
}

/// Regression for the remaining implicit history walk: this calls the kernel checking entry used by
/// explicit `transport`, with no smart tactic/planner. Each query names the
/// entry state and current state in constant space; the input contains
/// N stores and N checks, not an explicitly enumerated N-by-N history proof.
#[test]
fn repeated_pointer_frame_queries_have_near_linear_total_work() {
    let samples = repeated_pointer_frame_work(true, false);
    eprintln!("entry-to-current pointer checks: {samples:?}");
    // Doubling permits 2x linear work plus ample logarithmic overhead, but
    // rejects a sustained quadratic curve (approximately 4x).
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3,
            "pointer-frame checking exceeds the near-linear doubling envelope: {samples:?}"
        );
    }
}

#[test]
fn explicit_pointer_frame_composition_has_near_linear_total_work() {
    let samples = repeated_pointer_frame_work(false, true);
    eprintln!("explicit pointer frame composition: {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3,
            "explicit composition: {samples:?}"
        );
    }
}

#[test]
fn cold_pointer_frame_refusals_do_not_scan_history() {
    for overwrite in [None, Some(0), Some(4)] {
        let mut samples = Vec::new();
        for size in [4_u32, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let field = Pointer::symbolic(Variable(998_920));
            let write = Pointer::symbolic(Variable(998_921));
            let initial = crate::kernel::intern_memory(Memory::new().store(
                field.clone(),
                ProgramValue::typed_pointer(
                    Pointer::symbolic(Variable(998_922)),
                    ProgramType::Int32Pointer,
                ),
            ));
            let mut memory = initial.memory().clone();
            if let Some(offset) = overwrite {
                memory = memory.store(
                    field.offset_by_bytes(offset),
                    ProgramValue::Int32(9u32.into()),
                );
            }
            for index in 0..size {
                memory = memory.store(write.clone(), ProgramValue::Int32(index.into()));
            }
            let current = crate::kernel::intern_memory(memory);
            let facts = PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                    field.clone(),
                    0u32.into(),
                    8u32.into(),
                    1,
                ))),
                right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                    write,
                    0u32.into(),
                    4u32.into(),
                    1,
                ))),
            });
            let before = Pointer::loaded_value(&initial, &field);
            let after = Pointer::loaded_value(&current, &field);
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                    &before, &after, &facts,
                )
            });
            assert!(
                !proved,
                "an unrecorded history must not establish equality: {overwrite:?}"
            );
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{overwrite:?}: {samples:?}"
        );
    }
}

/// Query the same read-validity index used by ordinary typed loads and call
/// initialization. Store construction and premise admission are outside the
/// measurement: the charged work is only N constant-size checking queries.
/// Keep one source in the bucket so ambiguous-source refusal cannot hide the walk.
fn repeated_read_initialization_work(adjacent: bool, exact: bool) -> Vec<(u32, usize)> {
    let mut samples = Vec::new();
    for size in [16u32, 32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let read = Pointer {
            block: PointerBlock::Heap(998_940),
            offset: PointerOffsetTerm::Constant(0),
        };
        let write = Pointer {
            block: PointerBlock::Heap(998_941),
            offset: PointerOffsetTerm::Constant(0),
        };
        let initial = Memory::new();
        let defined = |memory: &Memory| {
            PureFactContext::new().assume_proposition(Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: read.clone(),
                value_type: ProgramType::Int32,
            })
        };
        let original = defined(&initial);
        let mut memory = initial;
        let mut total = 0;
        for index in 0..size {
            let previous = memory.clone();
            memory = memory.store_classed_with_context(
                write.clone(),
                int32(index),
                &PureFactContext::new(),
                None,
            );
            let facts = if exact {
                defined(&memory)
            } else if adjacent {
                defined(&previous)
            } else {
                original.clone()
            };
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.has_memory_read_defined_evidence(&memory, &read, ProgramType::Int32)
            });
            if adjacent || exact || index == 0 {
                assert!(proved, "read initialization at query {index} of {size}");
            } else {
                assert!(
                    !proved,
                    "long initialization history must need explicit links"
                );
            }
            total += work;
        }
        samples.push((size, total));
    }
    samples
}

#[test]
fn repeated_read_initialization_queries_have_near_linear_total_work() {
    let samples = repeated_read_initialization_work(false, false);
    eprintln!("entry-to-current read-initialization checks: {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3,
            "read-initialization checking exceeds the near-linear doubling envelope: {samples:?}"
        );
    }
}

#[test]
fn adjacent_read_initialization_queries_have_near_linear_total_work() {
    let samples = repeated_read_initialization_work(true, false);
    eprintln!("adjacent read-initialization checks: {samples:?}");
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 3, "adjacent control: {samples:?}");
    }
}

#[test]
fn exact_read_initialization_queries_have_near_linear_total_work() {
    let samples = repeated_read_initialization_work(false, true);
    eprintln!("exact read-initialization checks: {samples:?}");
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 3, "exact control: {samples:?}");
    }
}

/// Exercise the typed pointer-read constructor used by symbolic loads. All
/// stores are in the same object as the reads, but beyond their eight-byte
/// slots: the block memo cannot skip the history for every fresh cell at once.
/// Setup and exact read identities are outside the measurement; no cache is
/// cleared between reads. Each size starts a normal fresh verification session.
fn pointer_read_naming_samples(with_history: bool, same_cell: bool) -> Vec<(u32, usize)> {
    let mut samples = Vec::new();
    for size in [16u32, 32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: PointerBlock::Heap(998_960),
            offset: PointerOffsetTerm::Constant(0),
        };
        let initial = crate::kernel::intern_memory(Memory::new());
        let mut memory = initial.memory().clone();
        if with_history {
            for index in 0..size {
                memory = memory.store_classed_with_context(
                    base.offset_by_bytes(size * 8),
                    int32(index),
                    &PureFactContext::new(),
                    None,
                );
            }
        }
        let current = crate::kernel::intern_memory(memory);
        let reads = (0..size)
            .map(|index| {
                let address = base.offset_by_bytes(if same_cell { 0 } else { index * 8 });
                let read = Pointer::loaded_value(&current, &address);
                (address, read)
            })
            .collect::<Vec<_>>();
        let (values, work) = crate::instrumentation::measure_deterministic_work(|| {
            reads
                .iter()
                .map(|(address, read)| {
                    crate::kernel::PointerValue::from_read(
                        read.clone(),
                        ProgramType::Int32Pointer,
                        &current,
                        address,
                    )
                })
                .collect::<Vec<_>>()
        });
        // Construction keeps the exact supplied source even when an earlier
        // read would have the same bytes. No historical identity is inferred.
        for ((address, read), value) in reads.iter().zip(values.iter()) {
            assert_eq!(value.pointer(), read);
            let exact = Pointer::loaded_value(&current, address);
            assert_eq!(value.designation(), &exact);
            assert_eq!(value.opaque_extent(), Some(&exact));
        }
        samples.push((size, work));
    }
    samples
}

fn assert_pointer_read_naming_is_near_linear(samples: &[(u32, usize)]) {
    eprintln!("pointer-read naming (reads, work): {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 3,
            "pointer-read naming exceeds the near-linear doubling envelope: {samples:?}"
        );
    }
}

#[test]
fn fresh_pointer_read_naming_across_store_history_has_near_linear_total_work() {
    assert_pointer_read_naming_is_near_linear(&pointer_read_naming_samples(true, false));
}

#[test]
fn repeated_pointer_read_naming_of_one_cell_has_near_linear_total_work() {
    assert_pointer_read_naming_is_near_linear(&pointer_read_naming_samples(true, true));
}

#[test]
fn fresh_pointer_read_naming_without_store_history_has_near_linear_total_work() {
    assert_pointer_read_naming_is_near_linear(&pointer_read_naming_samples(false, false));
}

#[test]
fn symbolic_store_into_loaded_run_bounds_logical_slot_work() {
    for bounded in [false, true] {
        let mut samples = Vec::new();
        for count in [4u32, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = scaling_cell("local:loaded-run", 0);
            let source = crate::kernel::intern_memory(Memory::new());
            let memory = Memory::new()
                .with_block(base.block.clone(), count * 4)
                .with_seeded_cells(base.clone(), 4, ProgramType::Int32, 0, count, source);
            assert_eq!(memory.cells.runs_in_block(&base.block).count(), 1);
            let index = MachineTerm::Variable(Variable(999_900));
            let facts = if bounded {
                PureFactContext::new()
                    .assume_condition(
                        ConditionTerm::signed_less_equal(1u32.into(), index.clone()),
                        true,
                    )
                    .assume_condition(
                        ConditionTerm::signed_less_than(index.clone(), (count - 1).into()),
                        true,
                    )
            } else {
                PureFactContext::new()
            };
            let write = base.offset_by_elements(index, 4);
            let mut work = Vec::new();
            for _ in 0..3 {
                let (after, units) = crate::instrumentation::measure_deterministic_work(|| {
                    memory.without_possible_aliasing_cells(&write, 4, &facts)
                });
                let (forgotten_start, forgotten_count) =
                    if bounded { (4, count - 2) } else { (0, count) };
                assert!(after.has_initialized_bytes_at(
                    &base.offset_by_bytes(forgotten_start),
                    forgotten_count * 4
                ));
                assert!(!after.has_known_cell_at(&base.offset_by_bytes(4)));
                assert_eq!(after.has_known_cell_at(&base), bounded);
                assert_eq!(
                    after.has_known_cell_at(&base.offset_by_bytes((count - 1) * 4)),
                    bounded
                );
                assert!(
                    memory.has_known_cell_at(&base.offset_by_bytes(4)),
                    "the parent state stays intact"
                );
                work.push(units);
            }
            samples.push((count, work));
        }
        eprintln!("loaded run bounded={bounded}: {samples:?}");
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "{samples:?}"
        );
    }
}

#[test]
fn compact_run_store_does_not_scan_separation_candidates() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |i| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(999_950 + i)),
        };
        let base = pointer(0);
        let memory = Memory::new().with_seeded_cells(
            base.clone(),
            4,
            ProgramType::Int32,
            0,
            4,
            crate::kernel::intern_memory(Memory::new()),
        );
        assert_eq!(memory.cells.runs_in_block(&base.block).count(), 1);
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_proposition(Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(MemoryRange::new(
                    pointer(10 + 2 * i),
                    0u32.into(),
                    4u32.into(),
                ))),
                right: Box::new(Resource::Memory(MemoryRange::new(
                    pointer(11 + 2 * i),
                    0u32.into(),
                    4u32.into(),
                ))),
            });
        }
        let mut work = Vec::new();
        for _ in 0..3 {
            let (_, units) = crate::instrumentation::measure_deterministic_work(|| {
                memory.without_possible_aliasing_cells(&pointer(1), 4, &facts)
            });
            work.push(units);
        }
        samples.push((size, work));
    }
    eprintln!("compact-run separation misses: {samples:?}");
    assert!(
        samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
        "{samples:?}"
    );
}

#[test]
fn compact_run_store_declines_crowded_anchor_buckets() {
    let mut samples = Vec::new();
    for size in [4u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(999_930));
        let write = Pointer::symbolic(Variable(999_931));
        let memory = Memory::new().with_seeded_cells(
            base.clone(),
            4,
            ProgramType::Int32,
            0,
            4,
            crate::kernel::intern_memory(Memory::new()),
        );
        let separate = |count| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                base.clone(),
                0u32.into(),
                count,
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                write.clone(),
                0u32.into(),
                1u32.into(),
            ))),
        };
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_proposition(separate((4 + i).into()));
        }
        let mut work = Vec::new();
        for _ in 0..3 {
            let (after, units) = crate::instrumentation::measure_deterministic_work(|| {
                memory.without_possible_aliasing_cells(&write, 4, &facts)
            });
            assert!(!after.has_known_cell_at(&base));
            work.push(units);
        }
        samples.push((size, work));
        let selected = PureFactContext::new().assume_proposition(separate(4u32.into()));
        assert!(
            memory
                .without_possible_aliasing_cells(&write, 4, &selected)
                .has_known_cell_at(&base)
        );
        assert!(
            !memory
                .without_possible_aliasing_cells(&write, 8, &selected)
                .has_known_cell_at(&base),
            "stated write member must cover every written byte"
        );
        let partial = PureFactContext::new().assume_proposition(separate(1u32.into()));
        assert!(
            !memory
                .without_possible_aliasing_cells(&write, 4, &partial)
                .has_known_cell_at(&base),
            "stated run member must cover the complete run"
        );
        let aliased = selected.assume_condition(
            ConditionTerm::pointer_equal(base.clone(), write.clone()),
            true,
        );
        assert!(
            !memory
                .without_possible_aliasing_cells(&write, 4, &aliased)
                .has_known_cell_at(&base),
            "later aliasing must not preserve stale values"
        );
    }
    eprintln!("compact-run crowded anchors: {samples:?}");
    assert!(
        samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
        "{samples:?}"
    );
}

#[test]
fn compact_run_store_bounds_ownership_member_selection() {
    for explicit_owner in [false, true] {
        let mut samples = Vec::new();
        for size in [4u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(Variable(999_940));
            let write = Pointer::symbolic(Variable(999_941));
            let memory = Memory::new().with_seeded_cells(
                base.clone(),
                4,
                ProgramType::Int32,
                0,
                4,
                crate::kernel::intern_memory(Memory::new()),
            );
            let own = |base: Pointer, low: u32, high: u32| {
                ResourceFact::own_memory(MemoryRange::new(base, low.into(), high.into()))
            };
            let mut owner = ResourceContext::new().unchecked_with_fact(own(write.clone(), 0, 1));
            for i in 0..size {
                owner = owner.unchecked_with_fact(own(base.clone(), i * 4, (i + 1) * 4));
            }
            let mut facts = PureFactContext::new()
                .assume_proposition(Proposition::ResourceComposition(owner.clone()));
            if explicit_owner {
                facts = facts.with_store_owner(Some(owner));
            }
            let mut work = Vec::new();
            for _ in 0..3 {
                let (after, units) = crate::instrumentation::measure_deterministic_work(|| {
                    memory.without_possible_aliasing_cells(&write, 4, &facts)
                });
                assert!(!after.has_known_cell_at(&base));
                work.push(units);
            }
            samples.push((size, work));
            let singleton = ResourceContext::new()
                .unchecked_with_fact(own(base.clone(), 0, 4))
                .unchecked_with_fact(own(write.clone(), 0, 1));
            let facts = PureFactContext::new().with_store_owner(Some(singleton));
            assert!(
                memory
                    .without_possible_aliasing_cells(&write, 4, &facts)
                    .has_known_cell_at(&base)
            );
            assert!(
                !memory
                    .without_possible_aliasing_cells(&write, 8, &facts)
                    .has_known_cell_at(&base)
            );
        }
        eprintln!("compact-run owners explicit={explicit_owner}: {samples:?}");
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "{samples:?}"
        );
    }
}

#[test]
fn compact_run_live_footprint_bounds_prefix_and_hole_work() {
    use crate::kernel::{CellRun, IndexIntervals};
    let mut samples = Vec::new();
    for size in [4u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(999_960));
        let mut holes = IndexIntervals::default();
        holes.insert_range(0, size);
        for i in 0..size {
            holes.insert_range(size + 2 * i + 1, size + 2 * i + 2);
        }
        holes.insert_range(3 * size, 4 * size);
        let run = CellRun::new(
            base.clone(),
            4,
            ProgramType::Int32,
            4 * size,
            crate::kernel::intern_memory(Memory::new()),
            holes,
        );
        let (footprint, work) =
            crate::instrumentation::measure_deterministic_work(|| run.live_byte_footprint());
        assert_eq!(
            footprint,
            Some((base.offset_by_bytes(size * 4), (2 * size - 1) * 4))
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn compact_run_fixed_store_does_not_walk_holes() {
    use crate::kernel::{CellRun, IndexIntervals};
    let mut samples = Vec::new();
    for size in [4u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = scaling_cell("local:hole-run", 0);
        let mut holes = IndexIntervals::default();
        for i in 0..size {
            holes.insert_range(2 * i + 1, 2 * i + 2);
        }
        let run = CellRun::new(
            base.clone(),
            4,
            ProgramType::Int32,
            2 * size,
            crate::kernel::intern_memory(Memory::new()),
            holes,
        );
        let facts = PureFactContext::new();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::run_slots_kept_by_store(&run, &base, 4, &facts)
        });
        assert!(
            !result.1,
            "a complete write does not forget untouched bytes"
        );
        samples.push(work);
        assert!(crate::kernel::reasoning::run_slots_kept_by_store(&run, &base, 2, &facts).1);
        assert!(
            !crate::kernel::reasoning::run_slots_kept_by_store(
                &run,
                &base.offset_by_bytes(4),
                2,
                &facts,
            )
            .1,
            "a hole has no cached value to forget"
        );
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn compact_run_partial_store_checks_overlapping_value_widths() {
    use crate::kernel::{CellRun, IndexIntervals};
    let _session = crate::kernel::VerificationSession::enter();
    let base = scaling_cell("local:overlapping-run", 0);
    let mut holes = IndexIntervals::default();
    holes.insert_range(0, 1);
    holes.insert_range(2, 3);
    let run = CellRun::new(
        base.clone(),
        1,
        ProgramType::Int32,
        8,
        crate::kernel::intern_memory(Memory::new()),
        holes,
    );
    // Both boundary slots are holes, but the middle slot still loses bytes.
    assert!(
        crate::kernel::reasoning::run_slots_kept_by_store(
            &run,
            &base.offset_by_bytes(2),
            1,
            &PureFactContext::new(),
        )
        .1
    );
}

#[test]
fn wide_store_comparisons_keep_retained_arithmetic_and_exact_sources() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineOperandView,
        SharedMachineIntegerTerm,
    };
    for unsigned in [false, true] {
        let format = if unsigned {
            MachineIntegerType::UInt64
        } else {
            MachineIntegerType::Int64
        };
        let mut previous_work = None;
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut root = KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(999_300),
            );
            let one = KernelTerm::retained_native_machine_operand(
                format,
                &MachineTerm::int64_constant(1),
            );
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Subtract,
                    [root, one.clone()],
                );
            }
            let index = SharedMachineIntegerTerm::observe_shared(format, root.clone()).unwrap();
            let zero = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0.into()),
            };
            let selected = Pointer {
                block: zero.block.clone(),
                offset: PointerOffsetTerm::Int64Scaled {
                    value: index,
                    byte_width: 4,
                    unsigned,
                },
            };
            let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format,
                CompareRelation::Equal,
                [
                    MachineOperandView::Shared(&root),
                    MachineOperandView::Legacy(&MachineTerm::int64_constant(0)),
                ],
            );
            let empty = PureFactContext::new();
            let same = empty.clone().assume_condition(condition.clone(), true);
            let different = empty.clone().assume_condition(condition, false);
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(
                        crate::kernel::reasoning::pointers_directly_distinct_for_store(
                            &zero, &selected, &different
                        )
                    );
                    assert!(
                        crate::kernel::reasoning::pointers_directly_distinct_for_store(
                            &selected, &zero, &different
                        )
                    );
                    assert!(
                        !crate::kernel::reasoning::pointers_directly_distinct_for_store(
                            &zero, &selected, &empty
                        )
                    );
                    assert!(
                        !crate::kernel::reasoning::pointers_directly_distinct_for_store(
                            &zero, &selected, &same
                        )
                    );
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            // Sixteen selected queries may walk the selected arithmetic;
            // quadrupling that arithmetic must not cause superlinear work.
            if let Some(previous) = previous_work {
                assert!(
                    work <= previous * 5,
                    "size={size}, work={work}, previous={previous}"
                );
            }
            previous_work = Some(work);
        }
    }
}
