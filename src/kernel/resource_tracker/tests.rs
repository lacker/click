// The tracker answers about constructed histories here: each test builds the
// recorded edges directly, so a stop kind is pinned by the edge that produced
// it rather than by a proof that happens to reach it.
use super::*;
use crate::kernel::intern_c_memory;

fn block(name: &str) -> PointerBlock {
    PointerBlock::Concrete(name.to_string())
}

fn at(block: PointerBlock, offset: i64) -> Pointer {
    Pointer {
        block,
        offset: PointerOffsetTerm::Constant(offset),
    }
}

fn one() -> CValue {
    CValue::Int32(Bitvector32Term::Constant(1))
}

fn point(memory: &CMemory) -> ProgramPoint {
    ProgramPoint::at(&intern_c_memory(memory.clone()))
}

fn entry_memory() -> CMemory {
    CMemory::new()
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
            Resource::Cell {
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
            Resource::Block(&block("global:g")),
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
        Resource::Cell {
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
        let after = entry
            .clone()
            .store(written, CValue::UInt8(Bitvector32Term::Constant(7)));
        assert_ne!(
            same(
                Resource::Cell {
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
            Resource::Cell {
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
        Resource::Cell {
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
    let ranges = vec![CMemoryRange::new(
        at(block("global:g"), 0),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
    )];
    let after =
        entry
            .clone()
            .with_call_memory_havoc(Variable(901), &ranges, &PureFactContext::new());
    let outside = at(block("global:h"), 0);
    assert_eq!(
        same(
            Resource::Cell {
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
        Resource::Cell {
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
    let ranges = vec![CMemoryRange::new(
        at(block("global:g"), 0),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
    )];
    let after =
        entry
            .clone()
            .with_call_memory_havoc(Variable(903), &ranges, &PureFactContext::new());
    assert_eq!(
        same(
            Resource::Block(&block("global:h")),
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same,
        "another file-scope object is proven distinct from every range the call declared"
    );

    let outcome = same(
        Resource::Block(&block("global:g")),
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
        Resource::Block(&PointerBlock::ExternalArgument),
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
/// forgetting a cached value removes what the newer snapshot knows, and the
/// argument names the older one, whose values stay true of an object the write
/// set excludes.
///
/// This is a unit test because no C loop reaches it yet: the loop rule
/// assembles its abstract head memory by rebuilding the snapshot's maps, which
/// records no derivation edge, so the recorded execution stops connecting the
/// two points one step below the havoc.
#[test]
fn a_loop_havoc_carries_a_block_outside_its_checked_write_set() {
    let entry = entry_memory().store(at(block("global:h"), 0), one());
    let ranges = vec![CMemoryRange::new(
        at(block("global:g"), 0),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
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
            Resource::Block(&block("global:h")),
            &point(&after),
            &point(&entry)
        ),
        Sameness::Same,
        "a checked write set in another object leaves this one's contents alone"
    );
    let outcome = same(
        Resource::Block(&block("global:g")),
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
        Resource::Cell {
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
            Resource::Cell {
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
            Resource::Block(&block("global:g")),
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
    let outcome = same(Resource::Block(&subject), &point(&own), &point(&entry));
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
    let outcome = same(Resource::Block(&symbolic), &point(&after), &point(&entry));
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
        .with_heap_allocation_claim(fresh.clone(), 16)
        .expect("a fresh allocation claim");
    let freed = live
        .clone()
        .free_heap_block(&fresh, &PureFactContext::new())
        .expect("the allocation is live, so it can be released");

    // The release edge records a base that is not the pre-free state -- the
    // producer interns it after dropping the live entry -- so this asks the
    // walk directly whether it crossed the release rather than comparing two
    // program points across it.
    let crossed = last_same(Resource::Block(&block("global:g")), &point(&freed))
        .expect("a block always has a last-same point");
    assert_ne!(
        crossed.point,
        point(&freed),
        "a released heap object is proven distinct from a global, so the walk crosses it"
    );

    let own = last_same(Resource::Block(&heap), &point(&freed))
        .expect("a block always has a last-same point");
    assert_eq!(own.point, point(&freed));
    assert_eq!(own.stopped_by.change, Change::Free { allocation: fresh });
    assert_eq!(own.stopped_by.reason, StopReason::Affected);
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
        .with_heap_allocation_claim(inside.clone(), 16)
        .expect("a fresh allocation claim");
    let freed = live
        .free_heap_block(&inside, &PureFactContext::new())
        .expect("the allocation is live, so it can be released");
    let stopped = last_same(
        Resource::Block(&PointerBlock::ExternalArgument),
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
            Resource::Block(&block("global:g")),
            &point(&retired),
            &point(&entry)
        ),
        Sameness::Same,
        "another function-local object is proven distinct from a global"
    );
    let outcome = same(
        Resource::Block(&block("local:f:i")),
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
        Bitvector32Term::Constant(16),
        false,
    );
    assert_eq!(entry.blocks, requested.blocks);
    assert_eq!(entry.cells, requested.cells);
    assert_eq!(entry.union_cells, requested.union_cells);
    assert_eq!(
        entry.forgotten.ended_local_blocks,
        requested.forgotten.ended_local_blocks
    );
    let same_heap_but_pending = CHeapMemory {
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
                Resource::Block(&subject),
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
        Resource::Cell {
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
        Resource::Cell {
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
        Resource::Cell {
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
    let load = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(intern_c_memory(memory.clone()), Box::new(cell.clone()))
    };
    let fact = |memory: &CMemory| {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(load(memory)),
                Box::new(Bitvector32Term::Constant(5)),
            ),
            true,
        )
    };
    assert_eq!(
        version_mismatch(&fact(&after), &fact(&entry)),
        Some((
            // The fact spells a raw `MemoryLoad`, which carries no width, so
            // the resource stands in the widest scalar access.
            OwnedResource::Cell {
                pointer: cell.clone(),
                bytes: super::widest_scalar_access_bytes(),
            },
            point(&after),
            point(&entry)
        ))
    );
    assert_eq!(version_mismatch(&fact(&entry), &fact(&entry)), None);

    let other = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Constant(5)),
            Box::new(Bitvector32Term::Constant(5)),
        ),
        true,
    );
    assert_eq!(version_mismatch(&fact(&after), &other), None);
}

/// The version memos are keyed by interned snapshot, and interning dedups by
/// content, so an entry left behind by one verification would answer a
/// content-equal query in the next one from a history that verification never
/// built. `VerificationSession` clears them with the other canonical-form
/// caches.
#[test]
fn a_session_reset_empties_the_version_memos() {
    let memory = entry_memory().store(at(block("local:f:i"), 0), one());
    last_same_point(
        Resource::Block(&PointerBlock::ExternalArgument),
        &point(&memory),
    );
    assert!(
        block_epoch_memo_len() > 0,
        "the walk should have recorded its answer"
    );
    crate::kernel::memory_provenance::clear_canonical_form_caches();
    assert_eq!(
        block_epoch_memo_len(),
        0,
        "a session reset must not leave one verification's versions for the next"
    );
}

/// The kinds whose versions are values in two saved states rather than points
/// on the memory history: a model field and a counted population. They have no
/// naming walk and no recorded edge, so `same_at_states` is their whole
/// interface, and every answer here is one keyed lookup per state plus one term
/// comparison.
mod saved_states {
    use super::*;

    fn schema() -> ResourceFieldSchema {
        ResourceFieldSchema::new(vec![
            ("rank".into(), ResourceFieldType::C(CType::Int32)),
            ("mark".into(), ResourceFieldType::Integer),
        ])
        .unwrap()
    }

    fn instance(identity: u64, rank: u32, mark: i64) -> ResourceInstance {
        ResourceInstance::new(
            Variable(identity),
            "cell".into(),
            vec![CValue::Int32(Bitvector32Term::Constant(7)).into()].into(),
            schema(),
            vec![
                AlgebraicValue::C(CValue::Int32(Bitvector32Term::Constant(rank))),
                AlgebraicValue::Integer(IntegerTerm::constant(num_bigint::BigInt::from(mark))),
            ]
            .into(),
        )
        .unwrap()
    }

    fn holding(identity: u64, rank: u32, mark: i64) -> CState {
        CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own(CResource::Instance(instance(identity, rank, mark))),
        ))
    }

    fn rank() -> Resource<'static> {
        Resource::ModelField {
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

    /// A call that returned ownership kept the identity and replaced the field
    /// values. Nothing recorded says which step did it, so the answer is
    /// `Unknown` and never `Changed`: a refusal reads the step from the site
    /// that minted the new value.
    #[test]
    fn a_replaced_field_value_is_unknown_not_changed() {
        let entry = holding(1, 3, 0);
        let after = holding(1, 4, 0);
        assert_eq!(
            same_at_states(rank(), StatePoint::at(&after), StatePoint::at(&entry)),
            replaced(None),
            "neither stored value was minted as an arbitrary model, so no step is claimed"
        );
    }

    /// `unfold` consumed the instance, so the later state holds no field to
    /// read. A version that cannot be found is never reported the same: a
    /// field a contract did not promise must not become a premise.
    #[test]
    fn a_consumed_instance_is_unknown() {
        let entry = holding(1, 3, 0);
        let consumed = CState::new();
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
        let other = Resource::ModelField {
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
        let field = Resource::ModelField {
            identity: Variable(1),
            children: child,
            field_index: 0,
        };
        assert_eq!(
            same_at_states(field, StatePoint::at(&after), StatePoint::at(&entry)),
            not_held(true, true)
        );
    }

    fn population_state(count: u32) -> CState {
        CState::new().with_counted_population(
            "object_ref",
            vec![CValue::Int32(Bitvector32Term::Constant(7)).into()].into(),
            Bitvector32Term::Constant(count),
        )
    }

    /// A population's version is the `count` term the state holds, by the same
    /// keyed lookup every other consumer uses.
    #[test]
    fn a_population_count_is_its_version() {
        let arguments = [CValue::Int32(Bitvector32Term::Constant(7)).into()];
        let population = Resource::Population {
            name: "object_ref",
            arguments: &arguments,
        };
        let one = population_state(1);
        let same_count = population_state(1);
        let two = population_state(2);
        assert_eq!(
            same_at_states(
                population,
                StatePoint::at(&same_count),
                StatePoint::at(&one)
            ),
            Sameness::Same
        );
        assert_eq!(
            same_at_states(population, StatePoint::at(&two), StatePoint::at(&one)),
            Sameness::Unknown {
                at: None,
                why: Stop {
                    change: Change::PopulationMoved,
                    reason: StopReason::DifferentVersion,
                },
            }
        );
        let ended = CState::new();
        assert_eq!(
            same_at_states(population, StatePoint::at(&ended), StatePoint::at(&one)),
            not_held(true, false)
        );
        assert_eq!(
            sole_population_of_family(&one, "object_ref"),
            Some(OwnedResource::Population {
                name: "object_ref".to_string(),
                arguments: arguments.to_vec(),
            })
        );
        assert_eq!(sole_population_of_family(&ended, "object_ref"), None);
    }

    /// Neither kind has a naming path: no term is named by one of these
    /// points, so there is no oldest point to be, exactly as for a footprint.
    #[test]
    fn neither_kind_has_a_naming_walk() {
        let memory = entry_memory();
        let arguments = [CValue::Int32(Bitvector32Term::Constant(7)).into()];
        for resource in [
            rank(),
            Resource::Population {
                name: "object_ref",
                arguments: &arguments,
            },
        ] {
            assert!(last_same_point(resource, &point(&memory)).is_none());
            assert!(last_same(resource, &point(&memory)).is_none());
            assert!(resource.lives_in_a_saved_state());
        }
    }

    /// A question costs one keyed lookup per point, whatever the two states
    /// hold. Growing the states by unrelated instances and unrelated
    /// populations — the two things a question's key is *not* — leaves the work
    /// at two units, which is what would fail if this enumerated a resource
    /// context instead of indexing it.
    ///
    /// The deterministic work is measured, not estimated, and the question is
    /// answered at every size so the curve cannot be flattened by a run that
    /// decides nothing.
    #[test]
    fn a_saved_state_version_costs_one_lookup_per_point() {
        let unrelated = |size: u64, rank: u32| {
            let mut state = holding(1, rank, 0);
            for other in 0..size {
                state = state
                    .clone()
                    .with_resource_context(state.resources().clone().unchecked_with_fact(
                        CResourceFact::own(CResource::Instance(instance(100 + other, 7, 7))),
                    ))
                    .with_counted_population(
                        format!("family{other}"),
                        vec![CValue::Int32(Bitvector32Term::Constant(other as u32)).into()].into(),
                        Bitvector32Term::Constant(1),
                    );
            }
            state
        };
        for size in [8u64, 16, 32, 64] {
            let entry = unrelated(size, 3);
            let after = unrelated(size, 4);
            let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                same_at_states(rank(), StatePoint::at(&after), StatePoint::at(&entry))
            });
            assert_eq!(
                outcome,
                replaced(None),
                "size {size} must still be answered, or the curve measures nothing"
            );
            assert_eq!(
                work, 2,
                "size {size} cost {work} units; a question is one keyed lookup per point"
            );
        }
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
}

/// A footprint is the third resource the rule answers about, and it has no
/// naming walk: its one caller knows both ends of the interval it cares about
/// and asks at every step in between. So these ask the rule directly.
mod footprints {
    use super::*;
    use crate::kernel::resource_tracker::step_effect::{
        Evidence, FootprintSeparation, Separation, StepEffect, affects,
    };

    fn bytes(base: Pointer, count: u32) -> CMemoryRange {
        CMemoryRange::new_with_element_width(
            base,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(count),
            1,
        )
    }

    /// The rule's answer for the step that produced `after`, asked about a
    /// footprint that is `Some(ranges)` when the kernel could name it.
    fn effect(after: &CMemory, ranges: Option<&[CMemoryRange]>) -> StepEffect {
        let produced = intern_c_memory(after.clone());
        let derivation = produced
            .derivation()
            .expect("the constructed step records an edge");
        let no_facts = PureFactContext::new();
        affects(
            derivation.as_ref(),
            &produced,
            match ranges {
                Some(ranges) => Resource::Ranges(ranges),
                None => Resource::AnyMemory,
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
