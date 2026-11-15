// The tracker answers about constructed histories here: each test builds the
// recorded edges directly, so a stop kind is pinned by the edge that produced
// it rather than by a proof that happens to reach it.
use super::*;
use crate::kernel::intern_memory;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn block(name: &str) -> PointerBlock {
    PointerBlock::Concrete(name.to_string())
}

fn at(block: PointerBlock, offset: i64) -> Pointer {
    Pointer {
        block,
        offset: PointerOffsetTerm::Constant(offset),
    }
}

fn one() -> ProgramValue {
    ProgramValue::Int32(MachineTerm::constant(1))
}

fn point(memory: &Memory) -> VersionPoint {
    VersionPoint::at(&intern_memory(memory.clone()))
}

fn entry_memory() -> Memory {
    Memory::new()
        .with_block(block("global:g"), 16)
        .with_block(block("global:h"), 16)
        .with_block(block("local:f:i"), 4)
}

/// A store the kernel proves is in another object leaves both a cell and a
/// block fact alone, so both points name one version.
#[test]
fn a_store_to_another_object_keeps_one_version() {
    let entry = entry_memory();
    let after = entry.clone().store(at(block("local:f:i"), 0), one());
    let cell = at(block("global:g"), 0);
    assert_eq!(
        same(
            TrackedResource::Cell {
                pointer: &cell,
                bytes: 4
            },
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same
    );
    assert_eq!(
        same(
            TrackedResource::Block(&block("global:g")),
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same
    );
}

/// A store to the queried address changed it, and the answer names the
/// address that was written.
#[test]
fn a_store_to_the_cell_reports_changed() {
    let entry = entry_memory();
    let written = at(block("global:g"), 0);
    let after = entry.clone().store(written.clone(), one());
    let outcome = same(
        TrackedResource::Cell {
            pointer: &written,
            bytes: 4,
        },
        &point(&after),
        &point(&entry),
    );
    let Sameness::Changed { at: stopped, by } = outcome else {
        panic!("a store to the cell is a change, not {outcome:?}");
    };
    assert_eq!(stopped, Some(point(&after)));
    assert_eq!(
        by.change,
        Change::Store {
            pointer: written.clone()
        }
    );
    assert_eq!(by.reason, StopReason::Affected);
}

/// A narrow store inside a wide cell changed it, whatever the addresses are
/// called. Carrying a width on a cell resource is exactly what makes this
/// answer reachable: `global:g + 4` is a different address from `global:g` by
/// every ladder there is, and it writes the fifth byte of the eight-byte cell
/// at `global:g`. The same store does miss a four-byte cell there.
#[test]
fn a_narrow_store_inside_a_wide_cell_reports_changed() {
    let entry = entry_memory();
    let cell = at(block("global:g"), 0);
    for offset in 1..8 {
        let written = at(block("global:g"), offset);
        let after = entry.clone().store(written, crate::kernel::uint8(7));
        assert_ne!(
            same(
                TrackedResource::Cell {
                    pointer: &cell,
                    bytes: 8,
                },
                &point(&after),
                &point(&entry)
            ),
            Sameness::Same,
            "a one-byte store at offset {offset} writes the eight-byte cell at offset 0"
        );
        let four_byte_answer = same(
            TrackedResource::Cell {
                pointer: &cell,
                bytes: 4,
            },
            &point(&after),
            &point(&entry),
        );
        if offset >= 4 {
            assert_eq!(
                four_byte_answer,
                Sameness::Same,
                "a one-byte store at offset {offset} misses the four-byte cell at offset 0"
            );
        } else {
            assert_ne!(
                four_byte_answer,
                Sameness::Same,
                "a one-byte store at offset {offset} writes the four-byte cell at offset 0"
            );
        }
    }
}

/// A store through a spelling the kernel cannot separate from the cell is
/// `Unknown`, not `Changed`: the cell may well be untouched, and what is
/// missing is a proof of distinctness, which the answer names.
#[test]
fn a_store_that_may_alias_reports_unknown_and_the_check_it_needs() {
    let entry = entry_memory();
    let written = at(PointerBlock::Symbolic(Variable(77)), 0);
    let after = entry.clone().store(written.clone(), one());
    let cell = at(block("global:g"), 0);
    let outcome = same(
        TrackedResource::Cell {
            pointer: &cell,
            bytes: 4,
        },
        &point(&after),
        &point(&entry),
    );
    let Sameness::Unknown { at: stopped, why } = outcome else {
        panic!("an unseparated store is unknown, not {outcome:?}");
    };
    assert_eq!(stopped, Some(point(&after)));
    assert_eq!(why.change, Change::Store { pointer: written });
    assert_eq!(
        why.reason,
        StopReason::NotShownSeparate(SeparationCheck::PointerDistinctness)
    );
}

/// A call's checked write set is separation evidence for a cell outside it,
/// and the reason a cell inside it cannot be carried.
#[test]
fn a_call_havoc_carries_a_cell_outside_its_write_set_only() {
    let entry = entry_memory();
    let ranges = vec![MemoryRange::new(
        at(block("global:g"), 0),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
    )];
    let after =
        entry
            .clone()
            .with_call_memory_havoc(Variable(901), &ranges, &PureFactContext::new(), None);
    let outside = at(block("global:h"), 0);
    assert_eq!(
        same(
            TrackedResource::Cell {
                pointer: &outside,
                bytes: 4
            },
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same,
        "a cell in another object is outside every range the call declared"
    );

    let inside = at(block("global:g"), 0);
    let outcome = same(
        TrackedResource::Cell {
            pointer: &inside,
            bytes: 4,
        },
        &point(&after),
        &point(&entry),
    );
    let Sameness::Unknown { why, .. } = outcome else {
        panic!("a call that may write the cell is unknown, not {outcome:?}");
    };
    assert_eq!(why.change, Change::Call { ranges });
    assert_eq!(
        why.reason,
        StopReason::NotShownSeparate(SeparationCheck::RangeDisjointness)
    );
}

/// One rule, one answer: a checked write set entirely in objects proven
/// distinct from the subject carries both a cell and a whole block across a
/// call, and a write set in the subject's own object carries neither.
#[test]
fn a_call_havoc_carries_a_block_outside_its_write_set_only() {
    let entry = entry_memory();
    let ranges = vec![MemoryRange::new(
        at(block("global:g"), 0),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
    )];
    let after =
        entry
            .clone()
            .with_call_memory_havoc(Variable(903), &ranges, &PureFactContext::new(), None);
    assert_eq!(
        same(
            TrackedResource::Block(&block("global:h")),
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same,
        "another file-scope object is proven distinct from every range the call declared"
    );

    let outcome = same(
        TrackedResource::Block(&block("global:g")),
        &point(&after),
        &point(&entry),
    );
    let Sameness::Unknown { why, .. } = outcome else {
        panic!("a call that may write the block is unknown, not {outcome:?}");
    };
    assert_eq!(
        why.change,
        Change::Call {
            ranges: ranges.clone()
        }
    );
    assert_eq!(
        why.reason,
        StopReason::NotShownSeparate(SeparationCheck::WholeBlockAgreement)
    );

    // An array parameter and a global are two known, differing spellings of
    // possibly one object, so a write set naming the global separates from
    // neither.
    let outcome = same(
        TrackedResource::Block(&PointerBlock::ExternalArgument),
        &point(&after),
        &point(&entry),
    );
    assert!(
        matches!(outcome, Sameness::Unknown { .. }),
        "a global write set is not separate from an array argument, and got {outcome:?}"
    );
}

/// A loop havoc forgets this block's cached cell values whatever its write set
/// says, and is crossed all the same when the write set is in another object:
/// forgetting a cached value removes what the newer state knows, and the
/// argument names the older one, whose values stay true of an object the write
/// set excludes.
///
/// This is a unit test because no C loop reaches it yet: the loop rule
/// assembles its abstract head memory by rebuilding the state's maps, which
/// records no derivation edge, so the recorded execution stops connecting the
/// two points one step below the havoc.
#[test]
fn a_loop_havoc_carries_a_block_outside_its_checked_write_set() {
    let entry = entry_memory().store(at(block("global:h"), 0), one());
    let ranges = vec![MemoryRange::new(
        at(block("global:g"), 0),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
    )];
    let after = entry.clone().with_loop_memory_havoc_preserving_loans(
        Variable(904),
        &std::collections::BTreeSet::new(),
        Some(&ranges),
        None,
    );
    assert!(
        !after.has_known_cell_at(&at(block("global:h"), 0)),
        "the havoc drops the subject's cached values, which is what makes this the hard case"
    );
    assert_eq!(
        same(
            TrackedResource::Block(&block("global:h")),
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same,
        "a checked write set in another object leaves this one's contents alone"
    );
    let outcome = same(
        TrackedResource::Block(&block("global:g")),
        &point(&after),
        &point(&entry),
    );
    assert!(
        matches!(outcome, Sameness::Unknown { .. }),
        "the object the loop declared it may write is not carried, and got {outcome:?}"
    );
}

/// A loop with no checked footprint is an unconditional barrier, and the
/// answer says so rather than naming a separation nothing could supply.
#[test]
fn a_loop_without_a_write_set_needs_no_separation_check() {
    let entry = entry_memory();
    let after = entry.clone().with_loop_memory_havoc_preserving_loans(
        Variable(902),
        &std::collections::BTreeSet::new(),
        None,
        None,
    );
    let cell = at(block("global:g"), 0);
    let outcome = same(
        TrackedResource::Cell {
            pointer: &cell,
            bytes: 4,
        },
        &point(&after),
        &point(&entry),
    );
    let Sameness::Unknown { why, .. } = outcome else {
        panic!("an unchecked loop havoc is unknown, not {outcome:?}");
    };
    assert_eq!(why.change, Change::Loop { ranges: None });
    assert_eq!(
        why.reason,
        StopReason::NotShownSeparate(SeparationCheck::NoCheckedWriteSet)
    );
}

/// A bare declaration writes nothing, so one rule carries both resources
/// across it: the declared object has its own `blocks` key, and a block
/// proven distinct from it keeps its extent, cells, overlays, liveness and
/// heap status. `mdtests/array_fact_survives_a_declaration.md` is the user's
/// view of the same step.
#[test]
fn a_declaration_of_another_object_keeps_one_version() {
    let entry = entry_memory();
    let after = entry.clone().with_block(block("local:f:t"), 4);
    let cell = at(block("global:g"), 0);
    assert_eq!(
        same(
            TrackedResource::Cell {
                pointer: &cell,
                bytes: 4
            },
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same,
        "a declaration writes no cell"
    );
    assert_eq!(
        same(
            TrackedResource::Block(&block("global:g")),
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same,
        "a declaration of another object writes nothing this block contains"
    );
}

/// The block's *own* declaration is the step that created it, so it is a
/// change rather than a missing separation — and a declaration nothing
/// separates from this block still stops the walk.
#[test]
fn a_block_does_not_cross_its_own_declaration_or_an_unseparated_one() {
    let entry = entry_memory();
    let own = entry.clone().with_block(block("global:k"), 16);
    let subject = block("global:k");
    let outcome = same(
        TrackedResource::Block(&subject),
        &point(&own),
        &point(&entry),
    );
    let Sameness::Changed { by, .. } = outcome else {
        panic!("a block's own declaration is a change, not {outcome:?}");
    };
    assert_eq!(
        by.change,
        Change::Declaration {
            block: block("global:k")
        }
    );
    assert_eq!(by.reason, StopReason::Affected);

    // A symbolic block is a logic variable later facts may constrain to any
    // address, so nothing separates it from the declared object.
    let symbolic = PointerBlock::Symbolic(Variable(81));
    let after = entry.clone().with_block(block("local:f:t"), 4);
    let outcome = same(
        TrackedResource::Block(&symbolic),
        &point(&after),
        &point(&entry),
    );
    let Sameness::Unknown { why, .. } = outcome else {
        panic!("an unseparated declaration stops a block fact, and got {outcome:?}");
    };
    assert_eq!(
        why.reason,
        StopReason::NotShownSeparate(SeparationCheck::WholeBlockAgreement)
    );
}

/// Releasing an object proven distinct from this one leaves everything the
/// block contains, so both resources cross it — and releasing the block's own
/// object is a change, not a missing separation.
///
/// A heap allocation is the reachable case: `mdtests/…_freeing_the_array.md` is
/// the user's view of the negative, and the positive is here because a `free`
/// of a distinct object is only reachable after a `malloc`, whose branch
/// continuation the recorded execution does not connect across.
#[test]
fn a_release_of_another_object_keeps_one_version() {
    let heap = PointerBlock::Heap(1);
    let fresh = Pointer {
        block: heap.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let live = entry_memory()
        .with_heap_allocation_claim(fresh.clone(), HeapExtent::int32(16))
        .expect("a fresh allocation claim");
    let freed = live
        .clone()
        .free_heap_block(&fresh, &PureFactContext::new())
        .expect("the allocation is live, so it can be released");

    // This asks the walk directly whether it crossed the release rather than
    // comparing two program points across it.
    let crossed = last_same(TrackedResource::Block(&block("global:g")), &point(&freed))
        .expect("a block always has a last-same point");
    assert_ne!(
        crossed.point,
        point(&freed),
        "a released heap object is proven distinct from a global, so the walk crosses it"
    );

    let own = last_same(TrackedResource::Block(&heap), &point(&freed))
        .expect("a block always has a last-same point");
    assert_eq!(own.point, point(&freed));
    assert_eq!(own.stopped_by.change, Change::Free { allocation: fresh });
    assert_eq!(own.stopped_by.reason, StopReason::Affected);
}

/// A release edge's base is the memory the `free` started from, with the
/// constructor that made it: a trace legend explains it, and a walk across
/// the release reaches the history before it. A base interned after the
/// release dropped its live entry was a state no constructor recorded,
/// printed as an internal error in every trace through a `free`.
#[test]
fn a_release_is_based_on_the_memory_it_started_from() {
    let fresh = Pointer {
        block: PointerBlock::Heap(1),
        offset: PointerOffsetTerm::Constant(0),
    };
    let live = entry_memory()
        .with_heap_allocation_claim(fresh.clone(), HeapExtent::int32(16))
        .expect("a fresh allocation claim");
    let before = intern_memory(live.clone());
    let freed = intern_memory(
        live.free_heap_block(&fresh, &PureFactContext::new())
            .expect("the allocation is live, so it can be released"),
    );
    let derivation = freed.derivation().expect("a release records its edge");
    let MemoryDerivation::HeapFreed { base, .. } = derivation.as_ref() else {
        panic!("a release records a `HeapFreed` edge");
    };
    assert_eq!(base, &before, "the edge starts from the pre-free memory");
    assert!(
        base.memory().diagnostic_construction().is_some(),
        "the base keeps the constructor that produced it"
    );
}

/// An allocation the caller's object could be a subrange of is not separate
/// from it: a contract may claim `ExternalArgument` memory, which is the block
/// every array parameter of a function shares.
#[test]
fn a_release_inside_the_argument_object_stops_a_block_fact() {
    let inside = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let live = entry_memory()
        .with_heap_allocation_claim(inside.clone(), HeapExtent::int32(16))
        .expect("a fresh allocation claim");
    let freed = live
        .free_heap_block(&inside, &PureFactContext::new())
        .expect("the allocation is live, so it can be released");
    let stopped = last_same(
        TrackedResource::Block(&PointerBlock::ExternalArgument),
        &point(&freed),
    )
    .expect("a block always has a last-same point");
    assert_eq!(
        stopped.point,
        point(&freed),
        "a release inside the argument object must stop the walk"
    );
    assert_eq!(
        stopped.stopped_by.reason,
        StopReason::Affected,
        "the object released is the one the fact reads through"
    );
}

/// A local's lifetime ending retires that object alone, so a block proven
/// distinct from it crosses the step and the retired block itself does not.
#[test]
fn a_lifetime_end_of_another_local_keeps_one_version() {
    let entry = entry_memory();
    let retired = entry.without_local_block(&block("local:f:i"));
    assert_eq!(
        same(
            TrackedResource::Block(&block("global:g")),
            &point(&retired),
            &point(&entry)
        ),
        Sameness::Same,
        "another function-local object is proven distinct from a global"
    );
    let outcome = same(
        TrackedResource::Block(&block("local:f:i")),
        &point(&retired),
        &point(&entry),
    );
    let Sameness::Changed { by, .. } = outcome else {
        panic!("a block's own lifetime ending is a change, not {outcome:?}");
    };
    assert_eq!(
        by.change,
        Change::LifetimeEnd {
            block: block("local:f:i")
        }
    );
    assert_eq!(by.reason, StopReason::Affected);
}

/// An allocation request with no address yet records only that request, and
/// nothing that decides what a read of a block sees consults it. The pin is
/// that the step changes no extent, no cell, no overlay, no liveness and no
/// heap status other than the pending maps.
#[test]
fn a_pending_allocation_records_nothing_a_block_can_observe() {
    let entry = entry_memory();
    let requested = entry.clone().with_pending_heap_allocation(
        Pointer {
            block: PointerBlock::Symbolic(Variable(1_000)),
            offset: PointerOffsetTerm::Constant(0),
        },
        HeapExtent::int32(16),
        false,
    );
    assert_eq!(entry.blocks, requested.blocks);
    assert_eq!(entry.cells, requested.cells);
    assert_eq!(entry.union_cells, requested.union_cells);
    assert_eq!(
        entry.forgotten.ended_local_blocks,
        requested.forgotten.ended_local_blocks
    );
    let same_heap_but_pending = HeapMemory {
        pending_allocations: entry.heap.pending_allocations.clone(),
        ..requested.heap.as_ref().clone()
    };
    assert_eq!(
        &same_heap_but_pending,
        entry.heap.as_ref(),
        "a pending request must change nothing else about the heap"
    );

    for subject in [
        PointerBlock::ExternalArgument,
        block("global:g"),
        PointerBlock::Symbolic(Variable(1_000)),
    ] {
        assert_eq!(
            same(
                TrackedResource::Block(&subject),
                &point(&requested),
                &point(&entry)
            ),
            Sameness::Same,
            "a pending request is separate from every block, including {subject:?}"
        );
    }
}

/// With one point and no second one to compare against, the tracker reports
/// the step that ended the last stretch of agreement — and reports `Same`
/// when the recorded history holds no such step.
#[test]
fn one_sided_explanation_reaches_the_beginning_of_the_history() {
    let entry = entry_memory();
    let cell = at(block("global:g"), 0);
    let explanation = explain_last_same(
        TrackedResource::Cell {
            pointer: &cell,
            bytes: 4,
        },
        &point(&entry),
    );
    assert_eq!(explanation.outcome, Sameness::Same);
    assert_eq!(explanation.there, None);

    let written = at(PointerBlock::Symbolic(Variable(78)), 0);
    let after = entry.store(written.clone(), one());
    let explanation = explain_last_same(
        TrackedResource::Cell {
            pointer: &cell,
            bytes: 4,
        },
        &point(&after),
    );
    let Some((_, stop)) = explanation.outcome.blocking_step() else {
        panic!("an unseparated store is a blocking step");
    };
    assert_eq!(stop.change, Change::Store { pointer: written });
    assert_eq!(
        explanation.resource,
        OwnedResource::Cell {
            pointer: cell,
            bytes: 4
        }
    );
}

/// The bounded report counts the steps it crossed after the blocking one
/// instead of listing them.
#[test]
fn an_explanation_counts_the_steps_it_crossed() {
    let entry = entry_memory();
    let blocked = entry
        .clone()
        .store(at(PointerBlock::Symbolic(Variable(79)), 0), one());
    let after = blocked
        .clone()
        .store(at(block("local:f:i"), 0), one())
        .store(at(block("global:h"), 0), one());
    let cell = at(block("global:g"), 0);
    let explanation = explain(
        TrackedResource::Cell {
            pointer: &cell,
            bytes: 4,
        },
        &point(&after),
        &point(&entry),
    );
    assert_eq!(
        explanation
            .outcome
            .blocking_step()
            .and_then(|(at, _)| at.cloned()),
        Some(point(&blocked))
    );
    assert_eq!(explanation.crossed_after, 2);
    assert_eq!(explanation.there, Some(point(&entry)));
}

/// Two facts that differ only in which version they read: the tracker names
/// the resource and both points, and refuses a pair that differs in anything
/// else.
#[test]
fn a_version_mismatch_names_the_resource_and_both_points() {
    let entry = entry_memory();
    let cell = at(block("global:g"), 0);
    let after = entry
        .clone()
        .store(at(PointerBlock::Symbolic(Variable(80)), 0), one());
    let load = |memory: &Memory| {
        MachineTerm::MemoryLoad(
            intern_memory(memory.clone()),
            Box::new(cell.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let fact = |memory: &Memory| {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(load(memory)),
                right: Box::new(MachineTerm::constant(5)),
            },
            true,
        )
    };
    assert_eq!(
        version_mismatch(&fact(&after), &fact(&entry)),
        Some((
            // This unobserved word read retains the conservative pointer-word
            // width. A typed producer can record its precise scalar width.
            OwnedResource::Cell {
                pointer: cell.clone(),
                bytes: crate::kernel::LoadKind::Int32.unrecorded_access_byte_width(),
            },
            point(&after),
            point(&entry)
        ))
    );
    assert_eq!(version_mismatch(&fact(&entry), &fact(&entry)), None);

    let other = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::constant(5)),
            right: Box::new(MachineTerm::constant(5)),
        },
        true,
    );
    assert_eq!(version_mismatch(&fact(&after), &other), None);
}

/// The version memos are keyed by interned state, and interning dedups by
/// content, so an entry left behind by one verification would answer a
/// content-equal query in the next one from a history that verification never
/// built. `VerificationSession` clears them with the other canonical-form
/// caches.
#[test]
fn a_session_reset_empties_the_version_memos() {
    let memory = entry_memory().store(at(block("local:f:i"), 0), one());
    last_same_version_point(
        TrackedResource::Block(&PointerBlock::ExternalArgument),
        &point(&memory),
    );
    assert!(
        block_version_memo_len() > 0,
        "the walk should have recorded its answer"
    );
    crate::kernel::memory_provenance::clear_canonical_form_caches();
    assert_eq!(
        block_version_memo_len(),
        0,
        "a session reset must not leave one verification's versions for the next"
    );
}

/// The kinds whose versions are values in two saved states rather than points
/// on the memory history: a model field. It has no naming walk and no recorded
/// edge, so `same_at_states` is its whole interface, and every answer here is one keyed lookup per state plus one term
/// comparison.
mod saved_states {
    use super::*;

    fn schema() -> ResourceFieldSchema {
        ResourceFieldSchema::new(vec![
            (
                "rank".into(),
                ResourceFieldType::Program(ProgramType::Int32),
            ),
            ("mark".into(), ResourceFieldType::Integer),
        ])
        .unwrap()
    }

    fn instance(identity: u64, rank: u32, mark: i64) -> ResourceInstance {
        ResourceInstance::new(
            Variable(identity),
            "cell".into(),
            vec![ProgramValue::Int32(MachineTerm::constant(7)).into()].into(),
            schema(),
            vec![
                AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::constant(rank))),
                AlgebraicValue::Integer(IntegerTerm::constant(num_bigint::BigInt::from(mark))),
            ]
            .into(),
        )
        .unwrap()
    }

    fn holding(identity: u64, rank: u32, mark: i64) -> ExecutionState {
        ExecutionState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own(Resource::Instance(instance(identity, rank, mark))),
        ))
    }

    fn rank() -> TrackedResource<'static> {
        TrackedResource::ModelField {
            identity: Variable(1),
            children: &[],
            field_index: 0,
        }
    }

    fn not_held(missing_here: bool, missing_there: bool) -> Sameness {
        Sameness::Unknown {
            at: None,
            why: Stop {
                change: Change::NotHeld {
                    missing_here,
                    missing_there,
                },
                reason: StopReason::NotHeld,
            },
        }
    }

    fn replaced(by: Option<crate::kernel::model_fields::ModelMint>) -> Sameness {
        Sameness::Unknown {
            at: None,
            why: Stop {
                change: Change::ModelReplaced { by },
                reason: StopReason::DifferentVersion,
            },
        }
    }

    /// One state is one point: the handle decides, and no state contents are
    /// compared to reach it.
    #[test]
    fn one_state_is_one_point() {
        let state = holding(1, 3, 0);
        let point = StatePoint::at(&state);
        assert_eq!(same_at_states(rank(), point, point), Sameness::Same);
    }

    /// Two states that store the same value at the one field asked about hold
    /// one version of it, even though the states are different objects and the
    /// other field differs. Only the asked-about key is read.
    #[test]
    fn equal_stored_values_are_one_version() {
        let entry = holding(1, 3, 0);
        let after = holding(1, 3, 9);
        assert_eq!(
            same_at_states(rank(), StatePoint::at(&after), StatePoint::at(&entry)),
            Sameness::Same
        );
    }

    /// `unfold` consumed the instance, so the later state holds no field to
    /// read. A version that cannot be found is never reported the same: a
    /// field a contract did not promise must not become a premise.
    #[test]
    fn a_consumed_instance_is_unknown() {
        let entry = holding(1, 3, 0);
        let consumed = ExecutionState::new();
        assert_eq!(
            same_at_states(rank(), StatePoint::at(&consumed), StatePoint::at(&entry)),
            not_held(true, false),
            "a value only the first point has lost can still be named at the second"
        );
        assert_eq!(
            same_at_states(rank(), StatePoint::at(&entry), StatePoint::at(&consumed)),
            not_held(false, true)
        );
    }

    /// A field of another instance is another resource: the identity is part
    /// of the key, so an instance the state does not hold answers `NotHeld`
    /// rather than reading the one it does.
    #[test]
    fn another_identity_is_another_resource() {
        let entry = holding(1, 3, 0);
        let after = holding(1, 3, 0);
        let other = TrackedResource::ModelField {
            identity: Variable(2),
            children: &[],
            field_index: 0,
        };
        assert_eq!(
            same_at_states(other, StatePoint::at(&after), StatePoint::at(&entry)),
            not_held(true, true)
        );
    }

    /// A parent-qualified path is not resolved by this lookup, so it fails
    /// closed rather than answering about the parent's own field.
    #[test]
    fn a_child_path_fails_closed() {
        let entry = holding(1, 3, 0);
        let after = holding(1, 3, 0);
        let child = &["left".to_string()];
        let field = TrackedResource::ModelField {
            identity: Variable(1),
            children: child,
            field_index: 0,
        };
        assert_eq!(
            same_at_states(field, StatePoint::at(&after), StatePoint::at(&entry)),
            not_held(true, true)
        );
    }

    /// A model field has no naming path: no term is named by one of these
    /// points, so there is no oldest point to be, exactly as for a footprint.
    #[test]
    fn a_model_field_has_no_naming_walk() {
        let memory = entry_memory();
        let resource = rank();
        assert!(last_same_version_point(resource, &point(&memory)).is_none());
        assert!(last_same(resource, &point(&memory)).is_none());
        assert!(resource.lives_in_a_saved_state());
    }

    /// The explanation a refusal is built from carries the answer and no
    /// program point, and nothing of the states themselves.
    #[test]
    fn an_explanation_carries_the_answer_and_no_state() {
        let entry = holding(1, 3, 0);
        let after = holding(1, 4, 0);
        let explanation = explain_at_states(rank(), StatePoint::at(&after), StatePoint::at(&entry));
        assert_eq!(explanation.here, None);
        assert_eq!(explanation.there, None);
        assert_eq!(explanation.crossed_after, 0);
        assert_eq!(explanation.outcome, replaced(None));
        assert_eq!(explanation.resource.as_resource(), rank());
        assert_eq!(
            format!("{:?}", StatePoint::at(&entry)),
            "StatePoint(<saved state>)"
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/resource_tracker/tests/saved_states.rs");
    }
}

/// A footprint is the third resource the rule answers about, and it has no
/// naming walk: its one caller knows both ends of the interval it cares about
/// and asks at every step in between. So these ask the rule directly.
mod footprints {
    use super::*;
    use crate::kernel::resource_tracker::step_effect::{
        Evidence, FootprintSeparation, Separation, StepEffect, affects,
    };

    fn bytes(base: Pointer, count: u32) -> MemoryRange {
        MemoryRange::new_with_element_width(
            base,
            MachineTerm::constant(0),
            MachineTerm::constant(count),
            1,
        )
    }

    /// The rule's answer for the step that produced `after`, asked about a
    /// footprint that is `Some(ranges)` when the kernel could name it.
    fn effect(after: &Memory, ranges: Option<&[MemoryRange]>) -> StepEffect {
        let produced = intern_memory(after.clone());
        let derivation = produced
            .derivation()
            .expect("the constructed step records an edge");
        let no_facts = PureFactContext::new();
        affects(
            derivation.as_ref(),
            &produced,
            match ranges {
                Some(ranges) => TrackedResource::Ranges(ranges),
                None => TrackedResource::AnyMemory,
            },
            &Evidence {
                assumptions: &no_facts,
                cross_loop_havoc: false,
            },
        )
    }

    /// A write into another object cannot make a fact derived from this one
    /// stale, so the projection built over it stays.
    #[test]
    fn a_store_in_another_object_is_separate_from_a_stated_footprint() {
        let after = entry_memory().store(at(block("global:h"), 0), one());
        let footprint = [bytes(at(block("global:g"), 0), 4)];
        assert_eq!(
            effect(&after, Some(&footprint)),
            StepEffect::Separate(Separation::Footprint(
                FootprintSeparation::StoreOutsideRanges
            ))
        );
    }

    /// A write inside the stated bytes is not separate from them, whatever
    /// else the two spellings have in common.
    #[test]
    fn a_store_inside_a_stated_footprint_is_not_separate_from_it() {
        let after = entry_memory().store(at(block("global:g"), 0), one());
        let footprint = [bytes(at(block("global:g"), 0), 4)];
        assert!(!matches!(
            effect(&after, Some(&footprint)),
            StepEffect::Separate(_)
        ));
    }

    /// A block a write could be in, because the caller chose its address,
    /// reaches every footprint. This is coarser than the cell and block arms
    /// on purpose: a footprint's answer is spent *removing* a resource fact,
    /// and removing one more often is the safe direction.
    #[test]
    fn a_store_through_an_argument_reaches_every_stated_footprint() {
        let after = entry_memory().store(at(PointerBlock::ExternalArgument, 64), one());
        let footprint = [bytes(at(block("global:g"), 0), 4)];
        assert!(!matches!(
            effect(&after, Some(&footprint)),
            StepEffect::Separate(_)
        ));
    }

    /// A pointer read from memory names whatever object was stored there, so a
    /// write through it reaches every footprint too. Its constant displacement
    /// says nothing about where it lands in another block: `q + 8` is `p + 0`
    /// when the stored `q` is `p - 8`.
    #[test]
    fn a_store_through_a_loaded_pointer_reaches_every_stated_footprint() {
        let cells = entry_memory();
        let source = intern_memory(cells.clone());
        let p = Pointer::loaded_value(&source, &at(block("global:cells"), 0));
        let q = Pointer::loaded_value(&source, &at(block("global:cells"), 8));
        let after = cells.store(q.offset_by_bytes(8), one());
        for footprint in [[bytes(p.clone(), 8)], [bytes(at(block("global:g"), 0), 4)]] {
            assert!(
                !matches!(effect(&after, Some(&footprint)), StepEffect::Separate(_)),
                "{footprint:?}"
            );
        }
    }

    /// Declaring an object writes no byte of any object that already existed,
    /// so it leaves every footprint alone — including one the kernel could not
    /// name, which nothing else is separate from.
    #[test]
    fn a_declaration_is_separate_from_every_footprint() {
        let after = entry_memory().with_block(block("local:f:j"), 4);
        let footprint = [bytes(at(block("global:g"), 0), 4)];
        let writes_nothing =
            StepEffect::Separate(Separation::Footprint(FootprintSeparation::WritesNothing));
        assert_eq!(effect(&after, Some(&footprint)), writes_nothing);
        assert_eq!(effect(&after, None), writes_nothing);
    }

    /// Nothing bounds a footprint the kernel could not name, so every step
    /// that writes a byte reaches it.
    #[test]
    fn an_unnamed_footprint_is_reached_by_every_write() {
        let after = entry_memory().store(at(block("global:h"), 0), one());
        assert!(!matches!(effect(&after, None), StepEffect::Separate(_)));
    }
}

/// A store at an index the path's facts place off a cell is crossed when the
/// cell's value is read on that path, and only there. The store dropped the
/// cached cell, so the state after it answers nothing by itself, and the
/// assumption-free naming walk stops at the store. Under `u != 0` the value
/// is the earlier `3`; under `u == 0` the store writes the cell, so it is the
/// stored `7`; with no fact about `u` there is none — never the `3`.
#[test]
fn a_cell_value_on_a_path_crosses_only_a_store_its_facts_place_elsewhere() {
    let cell = at(block("global:g"), 0);
    let index = MachineTerm::Variable(Variable(0));
    let written = Pointer {
        block: block("global:g"),
        offset: PointerOffsetTerm::scaled_int32_node(index.clone(), 4),
    };
    let three = ProgramValue::Int32(MachineTerm::constant(3));
    let no_facts = PureFactContext::new();
    let before = entry_memory().store(cell.clone(), three.clone());
    let after = before
        .clone()
        .without_possible_aliasing_cells(&written, 4, &no_facts)
        .store(
            written.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        );
    assert_eq!(after.known_value(&cell), None, "the store dropped the cell");
    let after = intern_memory(after);
    let index_is_zero = |value| {
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(index.clone(), MachineTerm::constant(0)),
            value,
        ))
    };
    assert_eq!(
        cell_value_on_path(&after, &cell, 4, &index_is_zero(false))
            .map(crate::kernel::ExecutionValue::into_native),
        None,
        "source discovery does not cross the cache-forgetting and store edges"
    );
    let effect = Proposition::MemoryMutatesOnly {
        before: before.clone(),
        after: after.memory().clone(),
        writes: vec![(written, 4)],
    };
    let (old, new, equality) = crate::kernel::tests::explicit_frame(
        &before,
        after.memory(),
        &cell,
        crate::kernel::ProgramType::Int32,
        &[effect],
        &crate::kernel::tests::explicit_signed_elements(
            cell.clone(),
            crate::kernel::ProgramType::Int32,
            index.clone(),
            MachineTerm::constant(0),
            index_is_zero(false),
        ),
    )
    .expect("explicit separation preserves the stored value");
    let (ProgramValue::Int32(old), ProgramValue::Int32(new), ProgramValue::Int32(three)) =
        (old, new, three)
    else {
        panic!("complete int32 observations");
    };
    let source = Proposition::ConditionIs(ConditionTerm::equal(old, three.clone()), true);
    assert!(crate::kernel::eval::holds_by_read_over_write(&source));
    let premises = [source, equality];
    let facts = crate::kernel::proof::ProofFacts::from_ordered(&premises);
    let condition = ConditionTerm::equal(new, three);
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &Proposition::ConditionIs(condition.clone(), true),
            &premises,
            &facts,
        )
        .is_ok(),
        "the explicit frame preserves the stored value 3"
    );
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &Proposition::ConditionIs(condition, false),
            &premises,
            &facts,
        )
        .is_err(),
        "preservation cannot establish a different stored value"
    );
    assert_eq!(
        cell_value_on_path(&after, &cell, 4, &index_is_zero(true))
            .map(crate::kernel::ExecutionValue::into_native),
        Some(ProgramValue::Int32(MachineTerm::constant(7)))
    );
    assert_eq!(cell_value_on_path(&after, &cell, 4, &no_facts), None);
}

#[test]
fn branch_join_preserves_uncached_reads_only_when_every_arm_agrees() {
    for bytes in [4, 8] {
        let cell = at(block("global:g"), 0);
        let other = at(block("global:h"), 0);
        let before = entry_memory();
        let first = before.clone().store(other.clone(), one());
        let second = before
            .clone()
            .store(other, ProgramValue::Int32(MachineTerm::constant(2)));
        let joined = first
            .clone()
            .with_interface_memory_havoc(
                Variable(981001),
                &std::collections::BTreeSet::<crate::kernel::PointerBlock>::new(),
                &[&first, &second],
            )
            .unwrap();
        assert!(joined.known_value(&cell).is_none());
        assert_eq!(
            same(
                TrackedResource::Cell {
                    pointer: &cell,
                    bytes
                },
                &point(&joined),
                &point(&before)
            ),
            Sameness::Same
        );
        // A partial overlap in any arm blocks the full-width read, including
        // when that arm was not chosen as the join's derivation base.
        let changed = second.store(
            at(cell.block.clone(), i64::from(bytes - 1)),
            crate::kernel::uint8(9),
        );
        let bad = first
            .clone()
            .with_interface_memory_havoc(
                Variable(981002),
                &std::collections::BTreeSet::<crate::kernel::PointerBlock>::new(),
                &[&first, &changed],
            )
            .unwrap();
        assert_ne!(
            same(
                TrackedResource::Cell {
                    pointer: &cell,
                    bytes
                },
                &point(&bad),
                &point(&before)
            ),
            Sameness::Same
        );
    }
}

#[test]
fn branch_join_identity_retains_inputs_through_read_projection() {
    let cell = at(block("global:g"), 0);
    let other = at(block("global:h"), 0);
    let before = entry_memory();
    let a = before.clone().store(other.clone(), one());
    let b = before
        .clone()
        .store(other.clone(), ProgramValue::Int32(MachineTerm::constant(2)));
    let unchanged = a
        .clone()
        .with_interface_memory_havoc(
            Variable(981010),
            &std::collections::BTreeSet::<crate::kernel::PointerBlock>::new(),
            &[&a, &b],
        )
        .unwrap();
    let c = a.store(
        cell.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
    );
    let d = b.store(
        cell.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(10)),
    );
    let changed = c
        .clone()
        .with_interface_memory_havoc(
            Variable(981010),
            &std::collections::BTreeSet::<crate::kernel::PointerBlock>::new(),
            &[&c, &d],
        )
        .unwrap();
    assert!(unchanged.known_value(&cell).is_none());
    assert!(changed.known_value(&cell).is_none());
    assert_ne!(unchanged, changed);
    let project = |memory: &Memory| {
        crate::kernel::reasoning::memory_resolution::canonical_memory_for_pointer_load(
            memory, &cell,
        )
    };
    assert_ne!(
        project(&unchanged),
        project(&changed),
        "a read projection must not erase the incoming histories"
    );
    assert!(
        !crate::kernel::reasoning::memory_resolution::memories_match_for_pointer_load(
            &unchanged, &changed, &cell
        )
    );
}

#[test]
fn branch_join_typed_agreement_checks_alias_premises_and_access_width() {
    let cell = at(block("global:g"), 0);
    let alias = Pointer {
        block: PointerBlock::Symbolic(Variable(981021)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = entry_memory();
    let left = intern_memory(before.clone().store(at(block("local:f:i"), 0), one()));
    let right = intern_memory(before.store(alias.clone(), one()));
    let bare = PureFactContext::new();
    let separated = bare.clone().assume_condition(
        ConditionTerm::pointer_equal(alias, at(cell.block.clone(), 8)),
        true,
    );
    let query = |facts: &PureFactContext, bytes| {
        cell_source::join_read_agreement(
            &left,
            &right,
            &cell,
            bytes,
            &step_effect::Evidence {
                assumptions: facts,
                cross_loop_havoc: false,
            },
        )
    };
    assert!(query(&bare, 8).is_none());
    let (a, b) = query(&separated, 8).expect("an alias eight bytes away misses the tag");
    assert!(a.checks_walk_from(&left, &cell, 8, &separated));
    assert!(b.checks_walk_from(&right, &cell, 8, &separated));
    assert!(
        !b.checks_walk_from(&right, &cell, 8, &bare),
        "the retained alias premise must be checked"
    );
    assert!(
        query(&separated, 16).is_none(),
        "the same write overlaps a wider read"
    );
}

/// Naming walks share one empty context for the session, but a context built
/// against a replaced logical-read table would miss every read registered
/// after the replacement, so it is rebuilt then.
#[test]
fn naming_walks_share_one_context_until_the_read_table_is_replaced() {
    let _session = crate::kernel::VerificationSession::enter();
    let first = naming_context();
    assert!(std::rc::Rc::ptr_eq(&first, &naming_context()));
    crate::kernel::equality_graph::clear_logical_pointer_reads();
    assert!(!std::rc::Rc::ptr_eq(&first, &naming_context()));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/resource_tracker/tests.rs");
}

#[test]
fn transport_diagnostic_retains_the_actual_cell_walk_and_scope() {
    use crate::kernel::{
        take_transport_cell_walk_diagnostics, with_transport_cell_walk_diagnostics,
    };
    let entry = intern_memory(entry_memory());
    let pointer = at(block("global:g"), 0);
    let changed = intern_memory(entry.memory().clone().store(pointer.clone(), one()));
    let after = intern_memory(
        changed
            .memory()
            .clone()
            .store(at(block("local:f:i"), 0), one()),
    );
    let assumptions = PureFactContext::default();
    with_transport_cell_walk_diagnostics(|| {
        for _ in 0..2 {
            super::cell_source::memory_dag_cell_source_with_stop(
                &after,
                &pointer,
                4,
                &assumptions,
                true,
            )
            .unwrap();
        }
        // An inner check owns its observations, including after an unwind.
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            with_transport_cell_walk_diagnostics(|| {
                super::cell_source::memory_dag_cell_source_with_stop(
                    &entry,
                    &pointer,
                    4,
                    &assumptions,
                    true,
                )
                .unwrap();
                let inner = take_transport_cell_walk_diagnostics();
                assert_eq!(inner.len(), 1);
                assert_eq!(inner[0].stopped_at, entry);
                assert_eq!(
                    inner[0].reason,
                    "step not proved separate from the queried bytes"
                );
                panic!("restore outer collector");
            });
        }));
        let observations = take_transport_cell_walk_diagnostics();
        assert_eq!(
            observations.len(),
            1,
            "identical observations share one record"
        );
        let walk = &observations[0];
        assert_eq!(walk.start, after);
        assert_eq!(walk.stopped_at, changed);
        assert_eq!(walk.pointer, pointer);
        assert_eq!(walk.bytes, 4);
        assert_eq!(walk.crossed, 1);
        assert_eq!(walk.reason, "hop limit reached");
    });
    assert!(take_transport_cell_walk_diagnostics().is_empty());
}

#[test]
fn named_cell_stop_retains_the_decision_made_by_its_walk() {
    let _session = crate::kernel::VerificationSession::enter();
    let read = Pointer::symbolic(crate::kernel::Variable(981_201));
    let write = Pointer::symbolic(crate::kernel::Variable(981_202));
    let memory = intern_memory(Memory::new().store(write.clone(), one()));
    let here = VersionPoint::at(&memory);
    let named = last_same_named_cell(&read, 4, &here).expect("named cell");
    assert!(matches!(
        named.stopped_by.reason,
        StopReason::NotShownSeparate(_)
    ));

    // Producer definitions may grow the shared naming graph after the walk.
    // Reading its retained decision must neither reclassify the stop nor
    // re-enter that graph, which a read-definition consumer can already hold.
    naming_context()
        .equality_graph
        .add_checked_read_equality(&read, &write);
    let (retained, work) = crate::instrumentation::measure_deterministic_work(|| {
        last_same(
            TrackedResource::Cell {
                pointer: &read,
                bytes: 4,
            },
            &here,
        )
        .expect("retained stop")
    });
    assert_eq!(retained, named);
    assert_eq!(
        work, 0,
        "a retained stop runs no equality or history checks"
    );
}

#[test]
fn a_forgotten_observation_retains_only_its_complete_typed_value() {
    use super::cell_source::{CellWalkStop, memory_dag_cell_source_with_stop};
    use crate::kernel::{LoadKind, ProgramType};
    crate::kernel::memory_provenance::with_extended_dag_bridging(|| {
        let pointer = at(block("global:g"), 0);
        let source = intern_memory(entry_memory());
        let observed = source.memory().clone().materialize_cell_from_source(
            pointer.clone(),
            ProgramType::Int32,
            source.clone(),
        );
        let value = observed.known_value(&pointer).unwrap();
        let assumptions = PureFactContext::new();
        let forgotten = intern_memory(observed.without_possible_aliasing_cells(
            &pointer.offset_by_bytes(1),
            1,
            &assumptions,
        ));
        let (cell, stop) =
            memory_dag_cell_source_with_stop(&forgotten, &pointer, 4, &assumptions, true).unwrap();
        assert_eq!(stop, CellWalkStop::RetainedValue);
        assert_eq!(cell.resolved_value(&pointer, LoadKind::Int32), Some(value));
        assert!(cell.resolved_value(&pointer, LoadKind::Bits64).is_none());
        assert!(cell.checks_walk_from(&forgotten, &pointer, 4, &assumptions));
        let (wide, stop) =
            memory_dag_cell_source_with_stop(&forgotten, &pointer, 8, &assumptions, true).unwrap();
        assert_ne!(stop, CellWalkStop::RetainedValue);
        assert!(wide.resolved_value(&pointer, LoadKind::Bits64).is_none());
        let changed = intern_memory(forgotten.memory().clone().store(pointer.clone(), one()));
        let (cell, stop) =
            memory_dag_cell_source_with_stop(&changed, &pointer, 4, &assumptions, true).unwrap();
        assert_eq!(stop, CellWalkStop::Affected);
        assert_eq!(cell.resolved_value(&pointer, LoadKind::Int32), Some(one()));
        let load =
            |memory| MachineTerm::MemoryLoad(memory, Box::new(pointer.clone()), LoadKind::Int32);
        assert!(
            crate::kernel::explicit_atomic_equality_from_memory_derivations(
                &load(source.clone()),
                &load(forgotten),
                &assumptions,
            )
        );
        assert!(
            !crate::kernel::explicit_atomic_equality_from_memory_derivations(
                &load(source),
                &load(changed),
                &assumptions,
            )
        );
    });
}

#[test]
fn structural_read_dependencies_keep_the_observed_point_and_exact_width() {
    let _session = crate::kernel::VerificationSession::enter();
    let entry = entry_memory();
    let pointer = at(block("global:g"), 0);
    let origin = intern_memory(entry.store(at(block("global:h"), 0), one()));
    crate::kernel::eval::record_load_access_width(origin.memory(), &pointer, 4);
    let read = crate::kernel::eval::canonical_form_of_load(
        origin.clone(),
        pointer.clone(),
        LoadKind::Int32,
    );
    let MachineTerm::MemoryLoad(selected, _, _) = &read else {
        panic!("structural read")
    };
    assert_ne!(
        selected, &origin,
        "selection should cross the unrelated store"
    );
    let fact = Proposition::ConditionIs(ConditionTerm::equal(read.clone(), 0u32.into()), true);
    let reads = reads_of_proposition(&fact);
    assert_eq!(reads.len(), 1);
    assert_eq!(reads[0].resource, OwnedResource::Cell { pointer, bytes: 4 });
    assert_eq!(reads[0].point, VersionPoint::at(&origin));
    assert_eq!(crate::kernel::eval::load_variable_registry_len(), 0);
}

/// A read's version point does not depend on which point was asked first.
/// A loop that writes only `g` leaves `h` alone, as the block rule says; a
/// cell of `h` crosses it too, so a read of `h[0]` after a store to `h[1]`
/// and one right after the loop name the same point in either order.
#[test]
fn a_cell_version_point_is_the_same_whichever_point_is_asked_first() {
    let entry = entry_memory();
    let ranges = vec![MemoryRange::new(
        at(block("global:g"), 0),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
    )];
    let after_loop = entry.clone().with_loop_memory_havoc_preserving_loans(
        Variable(904),
        &std::collections::BTreeSet::new(),
        Some(&ranges),
        None,
    );
    let after_store = after_loop.clone().store(at(block("global:h"), 4), one());
    let cell = at(block("global:h"), 0);
    let ask =
        |memory: &Memory| cell_last_same_version_point(&intern_memory(memory.clone()), &cell, 4);
    clear_version_memos();
    let store_first = (ask(&after_store), ask(&after_loop));
    clear_version_memos();
    let after_loop_answer = ask(&after_loop);
    let loop_first = (ask(&after_store), after_loop_answer);
    assert_eq!(store_first, loop_first);
    assert_eq!(store_first.0, store_first.1);
    assert_ne!(
        store_first.0,
        Some(intern_memory(after_loop.clone())),
        "a loop that writes only `g` is crossed by a read of `h`"
    );
}

#[test]
fn retained_boolean_dependencies_keep_read_order_and_opaque_calls() {
    use crate::kernel::{
        BooleanOperandView, KernelTermImport, PureFunctionArgument, SharedPureApplication,
    };
    let memory = intern_memory(entry_memory());
    let read = |name| {
        MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(at(block(name), 0)),
            LoadKind::Int32,
        )
    };
    let source = ConditionTerm::BoolIf {
        condition: Box::new(ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Binary {
                format: MachineIntegerType::Int32,
                op: crate::kernel::MachineBinaryOp::Add,
                left: Box::new(read("global:g")),
                right: Box::new(read("global:h")),
            }),
            right: Box::new(MachineTerm::constant(0)),
        }),
        then_condition: Box::new(ConditionTerm::BoolApplication(
            SharedPureApplication::intern(
                "opaque_dependency".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Int32(read(
                    "local:f:i",
                )))],
            ),
        )),
        else_condition: Box::new(ConditionTerm::Constant(false)),
    };
    let root = KernelTermImport::default().condition(&source);
    let mut native = Vec::new();
    let mut shared = Vec::new();
    collect_condition_reads(&source, &mut native);
    collect_condition_operand_reads(BooleanOperandView::Shared(&root), &mut shared);
    assert_eq!(native.len(), 2);
    assert_eq!(shared, native);
}

#[test]
fn shared_offset_condition_resource_reads_keep_native_right_first_order() {
    use crate::kernel::{BooleanOperandView, KernelTermImport};
    let memory = intern_memory(entry_memory());
    let offset = |name| {
        PointerOffsetTerm::scaled_int32_node(
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(at(block(name), 0)),
                LoadKind::Int32,
            ),
            4,
        )
    };
    let source = ConditionTerm::PointerOffsetEqual(
        Box::new(PointerOffsetTerm::Add(
            Box::new(offset("global:g")),
            Box::new(offset("global:h")),
        )),
        Box::new(offset("local:f:i")),
    );
    let root = KernelTermImport::default().condition(&source);
    let mut expected = Vec::new();
    let mut actual = Vec::new();
    collect_condition_reads(&source, &mut expected);
    collect_condition_operand_reads(BooleanOperandView::Shared(&root), &mut actual);
    assert_eq!(expected.len(), 3);
    assert_eq!(actual, expected);
}

#[test]
fn raw_pointer_condition_reads_keep_block_and_displacement_order() {
    use crate::kernel::{BooleanOperandView, KernelTermImport};
    let memory = intern_memory(entry_memory());
    let offset = |name| {
        PointerOffsetTerm::scaled_int32_node(
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(at(block(name), 0)),
                LoadKind::Int32,
            ),
            4,
        )
    };
    let mut left = Pointer::loaded_value(&memory, &at(block("local:f:pointer_left"), 0));
    left.offset =
        PointerOffsetTerm::Add(Box::new(offset("global:g")), Box::new(offset("global:h")));
    let mut right = Pointer::loaded_value(&memory, &at(block("local:f:pointer_right"), 0));
    right.offset = offset("local:f:i");
    let source = ConditionTerm::PointerEqual(Box::new(left), Box::new(right));
    let root = KernelTermImport::default().condition(&source);
    let mut expected = Vec::new();
    let mut actual = Vec::new();
    collect_condition_reads(&source, &mut expected);
    collect_condition_operand_reads(BooleanOperandView::Shared(&root), &mut actual);
    assert_eq!(expected.len(), 5);
    assert_eq!(actual, expected);
}

#[test]
fn complete_pointer_conditions_keep_read_order() {
    use crate::kernel::{BooleanOperandView, KernelTermImport};
    let memory = intern_memory(entry_memory());
    let offset = |name| {
        PointerOffsetTerm::scaled_int32_node(
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(at(block(name), 0)),
                LoadKind::Int32,
            ),
            4,
        )
    };
    let mut left = Pointer::loaded_value(&memory, &at(block("local:f:pointer_left"), 0));
    left.offset =
        PointerOffsetTerm::Add(Box::new(offset("global:g")), Box::new(offset("global:h")));
    let mut right = Pointer::loaded_value(&memory, &at(block("local:f:pointer_right"), 0));
    right.offset = offset("local:f:i");
    let source = ConditionTerm::PointerValueEqual(
        Box::new(PointerValue::new(left, ProgramType::Int32Pointer)),
        Box::new(PointerValue::new(right, ProgramType::Int32Pointer)),
    );
    let root = KernelTermImport::default().condition(&source);
    let mut expected = Vec::new();
    let mut actual = Vec::new();
    collect_condition_reads(&source, &mut expected);
    collect_condition_operand_reads(BooleanOperandView::Shared(&root), &mut actual);
    assert_eq!(expected.len(), 5);
    assert_eq!(actual, expected);
}

#[test]
fn boolean_reads_report_only_the_one_byte_cell() {
    use crate::kernel::{BooleanOperandView, KernelTermImport};
    let memory = intern_memory(entry_memory());
    let pointer = Pointer {
        block: PointerBlock::Symbolic(Variable(999350)),
        offset: PointerOffsetTerm::scaled_int32_node(
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(at(block("global:g"), 0)),
                LoadKind::Int32,
            ),
            4,
        ),
    };
    let source = ConditionTerm::BoolLoad(memory, Box::new(pointer));
    let root = KernelTermImport::default().condition(&source);
    let mut native = Vec::new();
    let mut shared = Vec::new();
    collect_condition_reads(&source, &mut native);
    collect_condition_operand_reads(BooleanOperandView::Shared(&root), &mut shared);
    assert_eq!(native.len(), 1);
    assert_eq!(shared, native);
}
