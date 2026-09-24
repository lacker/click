//! Deterministic scaling regressions for kernel memory snapshots.
//!
//! A snapshot's maps are persistent and carry cached content hashes, so one
//! store, and interning the snapshot it produces, must cost work logarithmic
//! in the unrelated memory beside it rather than proportional to it. Each
//! test measures charged deterministic work at several sizes and prints the
//! numbers in its assertion messages.

use super::*;

const SIZES: [usize; 5] = [64, 128, 256, 512, 1024];

fn scaling_cell(block: &str, index: usize) -> Pointer {
    Pointer {
        block: PointerBlock::from(block),
        offset: PointerOffsetTerm::Constant(4 * index as i64),
    }
}

fn scaling_value(index: usize) -> CValue {
    CValue::UInt32(Bitvector32Term::Constant(index as u32))
}

/// A memory holding one cell in each of `count` unrelated blocks.
fn memory_with_unrelated_cells(count: usize) -> CMemory {
    (0..count).fold(CMemory::new(), |memory, index| {
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
            (0..size).fold(CMemory::new(), |memory, index| {
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
        let interned_base = intern_c_memory_ref(&base);
        // Derive the snapshot directly rather than through `store`, which
        // would already have interned it while recording its edge.
        let mut derived = base.clone();
        std::sync::Arc::make_mut(&mut derived.cells)
            .insert(scaling_cell("intern-target", 0), scaling_value(size));
        let (interned, work) =
            crate::instrumentation::measure_deterministic_work(|| intern_c_memory_ref(&derived));
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
        // snapshot and handed back its storage: equal snapshots carried by
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
        let forward_id = intern_c_memory_ref(&forward).arena_id();
        let backward_id = intern_c_memory_ref(&backward).arena_id();
        assert_eq!(
            forward_id, backward_id,
            "equal content must intern to one arena id at size {size}"
        );
        // The structural hit that deduplicated `backward` registered its
        // storage roots, so asking again is a shallow hit with no comparison.
        let (again, work) =
            crate::instrumentation::measure_deterministic_work(|| intern_c_memory_ref(&backward));
        assert_eq!(again.arena_id(), forward_id);
        rehits.push((size, work));
    }
    eprintln!("re-interning a deduplicated snapshot (N, units): {rehits:?}");
    assert!(
        rehits.iter().all(|(_, work)| *work == 0),
        "re-interning a structurally deduplicated snapshot must be a shallow hit: {rehits:?}"
    );
}

/// A statement executed twice from one base (planned, then checked) derives
/// the same snapshot twice. The second derivation is recognized as the base's
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
            resources.unchecked_with_fact(CResourceFact::own_allocation(heap_cell(identity, 0), 4))
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
fn with_initialized_allocation(memory: CMemory, identity: u64, value: u32) -> CMemory {
    let pending = Pointer {
        block: PointerBlock::Symbolic(Variable(identity)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let (memory, _, base) = memory
        .with_pending_heap_allocation(pending.clone(), Bitvector32Term::Constant(16), false)
        .resolve_pending_heap_allocation(&pending, true)
        .expect("the pending allocation resolves");
    assert_eq!(base, heap_cell(identity, 0));
    memory.store(base, CValue::UInt32(Bitvector32Term::Constant(value)))
}

/// `unrelated` live allocations, each holding one initialized cell, and the
/// target allocation with its first word written.
fn memory_with_unrelated_allocations(unrelated: usize) -> CMemory {
    let memory = (0..unrelated).fold(CMemory::new(), |memory, index| {
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
        // measured end to end in `src/surface/tests/scaling_tests.rs`.
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new(
                heap_cell(TARGET_HEAP, 0),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            ),
        ));
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let statement = CStatement::TypedStore {
            pointer: CExpression::Value(CValue::typed_pointer(
                heap_cell(TARGET_HEAP, 4),
                CType::UInt32Pointer,
            )),
            value: CExpression::Value(CValue::UInt32(Bitvector32Term::Constant(9))),
            value_type: CType::UInt32,
            volatile: false,
            pointee_constant: false,
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_c_statement_paths(
                &state,
                &statement,
                &PureFactContext::new(),
                &CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        let CStatementOutcome::Normal(stored) = &paths[0].outcome else {
            panic!("the heap store executes: {:?}", paths[0].outcome);
        };
        assert_eq!(stored.memory().cells.len(), size + 2);
        samples.push((size, work));
    }
    assert_constant_plus_log_growth("one C store into a heap block", &samples, 16.0);
}

fn target_range() -> CMemoryRange {
    CMemoryRange::new_with_element_width(
        heap_cell(TARGET_HEAP, 0),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(16),
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
            memory
                .clone()
                .with_call_memory_havoc(Variable(TARGET_HEAP + 1), &ranges, &assumptions)
        });
        assert_eq!(
            havocked.cells.len(),
            size,
            "only the target's cell is dropped"
        );
        produced.push((size, work));
        let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
            havocked.matches_call_memory_havoc_result(&memory, &ranges, &assumptions)
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
        // resource tracker's cell epoch walk), which is work in the length
        // of the history, one edge per transition, not in the size of the
        // memory. Measuring in a fresh session leaves that walk nothing to
        // cross, so what remains is the load's own work beside `size`
        // unrelated allocations.
        let memory = {
            let _build = crate::kernel::VerificationSession::enter();
            (0..size)
                .fold(CMemory::new(), |memory, index| {
                    with_initialized_allocation(memory, index as u64 + 1, index as u32)
                })
                .with_heap_allocation_claim(heap_cell(TARGET_HEAP, 0), 16)
                .expect("the claim registers")
                .store(
                    heap_cell(TARGET_HEAP, 0),
                    CValue::UInt32(Bitvector32Term::Constant(7)),
                )
        };
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let load = |offset| {
            crate::instrumentation::measure_deterministic_work(|| {
                evaluate_c_memory_load_paths(
                    &memory,
                    heap_cell(TARGET_HEAP, offset),
                    CType::UInt32,
                    Vec::new(),
                    Vec::new(),
                    &assumptions,
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
            CExpressionOutcome::Value(CValue::UInt32(Bitvector32Term::Constant(7)))
        );
        known.push((size, work));
        let (paths, work) = load(8);
        assert_eq!(paths.len(), 1, "{paths:?}");
        assert!(
            matches!(paths[0].outcome, CExpressionOutcome::Value(_)),
            "{:?}",
            paths[0].outcome
        );
        unknown.push((size, work));
    }
    assert_constant_plus_log_growth("one load of a known heap cell", &known, 16.0);
    assert_constant_plus_log_growth("one load of an unknown heap cell", &unknown, 16.0);
}
