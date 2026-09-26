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

/// Every pointer parameter lives in the one `ExternalArgument` block, so
/// neither the alias-candidate ranges nor the block-pair separation index
/// narrow a store through one parameter: each cached field of every other
/// parameter is a candidate. `count` parameter objects each have one cached
/// field, and the store goes through a borrowed field-bearing region (its
/// header object and its data range are two more owned members of the same
/// composition, like `examples/arena`'s `arena_write`).
fn owned_parameter_objects_and_a_region_store(
    count: usize,
) -> (CMemory, PureFactContext, Pointer, Vec<Pointer>) {
    let parameter = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(id)), 4),
    };
    let objects = (0..count)
        .map(|index| parameter(97_000 + index as u64))
        .collect::<Vec<_>>();
    let region = parameter(97_900);
    let data = parameter(97_901);
    let length = Bitvector32Term::Variable(Variable(97_902));
    let index = Bitvector32Term::Variable(Variable(97_903));
    let field = |object: &Pointer| object.offset_by_elements(Bitvector32Term::Constant(1), 4);
    let mut cells = objects.iter().map(field).collect::<Vec<_>>();
    cells.push(field(&region));
    let memory = cells
        .iter()
        .enumerate()
        .fold(CMemory::new(), |memory, (value, cell)| {
            memory.store(cell.clone(), scaling_value(value))
        });
    let object_range = |base: &Pointer, elements: u32| {
        CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(elements),
        )
    };
    let composition = objects
        .iter()
        .map(|object| CResourceFact::own_memory(object_range(object, 2)))
        .chain([
            CResourceFact::own_memory(object_range(&region, 3)),
            CResourceFact::own_memory(CMemoryRange::new(
                data.clone(),
                Bitvector32Term::Constant(0),
                length.clone(),
            )),
        ])
        .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index.clone(), length), true)
        .assume_proposition(Proposition::CResourceComposition(composition));
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
            .fold(CMemory::new(), |memory, (value, cell)| {
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
/// variables, so no snapshot or memo is shared between them.
#[test]
fn consecutive_reallocating_calls_cost_the_same_each() {
    const CALLS: [usize; 4] = [16, 64, 256, 1024];
    let external = |variable: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let int32_range = |base: &Pointer, end: u32| {
        CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(end),
            4,
        )
    };
    let bytes = Bitvector32Term::Constant(4);
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
            .unchecked_with_fact(CResourceFact::own_memory(int32_range(&other, 2)));
        let mut memory = CMemory::new();
        let mut total = 0;
        let mut last = 0;
        for call in 0..calls {
            let ranges = vec![int32_range(&owner, 2), int32_range(&data(call), 1)];
            let lent = ResourceContext::new()
                .unchecked_with_facts(ranges.iter().cloned().map(CResourceFact::own_memory));
            let (next, work) = crate::instrumentation::measure_deterministic_work(|| {
                let stale = crate::kernel::functions::caller_resource_left_stale_by_retirement(
                    &lent,
                    &kept,
                    &data(call),
                    &bytes,
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
                    .with_heap_allocation_claim(data(call + 1), bytes.clone())
                    .expect("a fresh claim");
                let point =
                    crate::kernel::resource_tracker::ProgramPoint::at(&intern_c_memory_ref(&next));
                for cell in [&field, &data(call + 1)] {
                    crate::kernel::resource_tracker::last_same_point(
                        crate::kernel::resource_tracker::Resource::Cell {
                            pointer: cell,
                            bytes: 4,
                        },
                        &point,
                    );
                }
                crate::kernel::resource_tracker::last_same_point(
                    crate::kernel::resource_tracker::Resource::Block(
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
        let named = crate::kernel::resource_tracker::last_same_point(
            crate::kernel::resource_tracker::Resource::Cell {
                pointer: &field,
                bytes: 4,
            },
            &crate::kernel::resource_tracker::ProgramPoint::at(&intern_c_memory_ref(&memory)),
        )
        .expect("the walk has an answer");
        assert!(
            matches!(
                named.snapshot().derivation().as_deref(),
                Some(CMemoryDerivation::CallHavoc { .. })
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
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(variable))),
            byte_width: 4,
        },
    };
    let int32_range = |base: &Pointer, end: u32| {
        CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(end),
            4,
        )
    };
    let data = external(5_300_000);
    let descriptor = external(5_300_001);
    let bytes = Bitvector32Term::Constant(8);
    let assumptions = PureFactContext::new();
    let lent = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(int32_range(&data, 2)));
    let view = CResourceFact::view_memory(int32_range(&descriptor, 3));
    let owned_and_viewed = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(int32_range(&descriptor, 3)))
        .unchecked_with_fact(view.clone());
    let (stale, work) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::functions::caller_resource_left_stale_by_retirement(
            &lent,
            &owned_and_viewed,
            &data,
            &bytes,
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
            &bytes,
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
            &bytes,
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
        let variable =
            |offset: u64| Bitvector32Term::Variable(Variable(96_000 + 3 * index + offset));
        facts
            .assume_condition(
                ConditionTerm::signed_less_equal(variable(0), Bitvector32Term::Constant(1_000)),
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
        Bitvector32Term::Variable(Variable(95_001)),
        Bitvector32Term::Variable(Variable(95_002)),
        Bitvector32Term::Variable(Variable(95_003)),
    );
    let symbolic = Pointer {
        block: PointerBlock::Symbolic(Variable(95_004)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let argument = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95_005)), 4),
    };
    let mut samples = Vec::new();
    for size in [64, 128, 256, 512] {
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
                    &Bitvector32Term::Constant(0),
                    &Bitvector32Term::Constant(1),
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
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(identity)), 4),
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

fn external_range(identity: u64, start: u32, end: u32) -> CMemoryRange {
    CMemoryRange::new(
        external_object(identity),
        Bitvector32Term::Constant(start),
        Bitvector32Term::Constant(end),
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
        CallKeptRanges::new(ResourceContext::new(), Vec::new()),
        &assumptions,
    );
    let memory = CMemory::new().store(
        external_field(KEPT_MEMBER, 8),
        CValue::Int32(Bitvector32Term::Constant(5)),
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
    // The cached value goes, as for any cell in the footprint's block; the
    // edge records the member that holds it, which is what names a later
    // load of it across the call.
    assert!(!havocked.has_known_cell_at(&external_field(KEPT_MEMBER, 8)));
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
fn measured_kept_members() -> [CResourceFact; 2] {
    [
        CResourceFact::own_memory(external_range(KEPT_MEMBER, 0, 12)),
        CResourceFact::own_memory(external_range(UNCACHED_MEMBER, 0, 4)),
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
                        CResourceFact::own_memory(CMemoryRange::new(
                            heap_cell(index as u64 + 1, 0),
                            Bitvector32Term::Constant(0),
                            Bitvector32Term::Constant(4),
                        )),
                        CResourceFact::view_memory(external_range(index as u64 + 1, 0, 4)),
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

/// The same record is linear in the residual members that can alias the
/// footprint: each owned member in the parameters' block is recorded once,
/// since the callee's footprint shares that block and only the caller's
/// ownership separates the member from it.
#[test]
fn a_call_records_kept_members_in_work_linear_in_the_aliasing_members() {
    let mut produced = Vec::new();
    let mut checked = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let residual = ResourceContext::new().unchecked_with_facts(
            (0..size)
                .map(|index| CResourceFact::own_memory(external_range(index as u64 + 1, 0, 4)))
                .chain(measured_kept_members()),
        );
        let (producer, checker) = kept_call_havoc_work(residual);
        produced.push((size, producer));
        checked.push((size, checker));
    }
    for (what, samples) in [
        ("a call havoc recording aliasing members", &produced),
        ("checking a call havoc recording aliasing members", &checked),
    ] {
        eprintln!("{what} (N, units): {samples:?}");
        for pair in samples.windows(2) {
            let [(small, small_work), (large, large_work)] = pair else {
                unreachable!()
            };
            assert!(
                (*large_work as f64) <= 1.5 * (*large as f64 / *small as f64) * *small_work as f64,
                "{what}: work grew faster than the aliasing members: {samples:?}"
            );
        }
    }
}

/// Placing a cell in a range an opened residual instance holds assumes that
/// instance's own facts, the premises that relate its fields to its cells: the
/// work is linear in the instance's body and nothing else.
#[test]
fn a_call_kept_instance_range_is_placed_in_work_linear_in_its_body() {
    const REGION: u64 = 4_000_000;
    const DATA: u64 = 4_100_000;
    const START_FIELD: u64 = 4_200_000;
    const START_LOAD: u64 = 4_300_000;
    let mut samples = Vec::new();
    for size in HEAP_SIZES {
        let _session = crate::kernel::VerificationSession::enter();
        let data = |index: Bitvector32Term| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(external_object(DATA).offset),
                Box::new(PointerOffsetTerm::scale_int32(index, 4)),
            ),
        };
        // `data[start..start + 1]`, spelled through the instance's field.
        let range = CMemoryRange::new(
            external_object(DATA),
            Bitvector32Term::Variable(Variable(START_FIELD)),
            Bitvector32Term::add(
                Bitvector32Term::Variable(Variable(START_FIELD)),
                Bitvector32Term::Constant(1),
            ),
        );
        // The body facts: `region->start == start` and `size` unrelated ones.
        let premises = std::iter::once((
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(START_LOAD))),
                Box::new(Bitvector32Term::Variable(Variable(START_FIELD))),
            ),
            true,
        ))
        .chain((0..size).map(|index| {
            (
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Variable(Variable(REGION + 1 + index as u64)),
                ),
                true,
            )
        }))
        .collect();
        let kept = CallKeptRanges::new(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(range)),
            premises,
        );
        let assumptions = PureFactContext::new();
        let cell = data(Bitvector32Term::Variable(Variable(START_LOAD)));
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
    for size in [64, 128, 256, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(94_100));
        let index = Bitvector32Term::Variable(Variable(94_101));
        let end = Bitvector32Term::Variable(Variable(94_102));
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
            let unrelated = Bitvector32Term::Variable(Variable(95_000 + i));
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
                contains(
                    &base.offset_by_int32_elements(Bitvector32Term::Variable(Variable(99_999))),
                ),
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

/// A kept range whose base is not one of the access's own spellings is
/// related to it by a proved base equality, asked once per fact set: every
/// walk across the call asks the same question about the same kept range,
/// and the repeats cost a keyed lookup, however many facts the proof holds.
#[test]
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
                .unchecked_with_facts([CResourceFact::own_memory(external_range(KEPT, 0, 4))]),
            Vec::new(),
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
            assumptions = assumptions.assume_proposition(Proposition::CResourceSeparate {
                left: CResource::Memory(external_range(2 * index + 1, 0, 4)),
                right: CResource::Memory(external_range(2 * index + 2, 0, 4)),
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
    let separation = |index: u64| Proposition::CResourceSeparate {
        left: CResource::Memory(external_range(2 * index + 1, 0, 4)),
        right: CResource::Memory(external_range(2 * index + 2, 0, 4)),
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
