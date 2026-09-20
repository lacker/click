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
        same(Resource::Cell(&cell), &point(&after), &point(&entry)),
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
    let outcome = same(Resource::Cell(&written), &point(&after), &point(&entry));
    let Sameness::Changed { at: stopped, by } = outcome else {
        panic!("a store to the cell is a change, not {outcome:?}");
    };
    assert_eq!(stopped, point(&after));
    assert_eq!(
        by.change,
        Change::Store {
            pointer: written.clone()
        }
    );
    assert_eq!(by.reason, StopReason::Affected);
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
    let outcome = same(Resource::Cell(&cell), &point(&after), &point(&entry));
    let Sameness::Unknown { at: stopped, why } = outcome else {
        panic!("an unseparated store is unknown, not {outcome:?}");
    };
    assert_eq!(stopped, point(&after));
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
        same(Resource::Cell(&outside), &point(&after), &point(&entry)),
        Sameness::Same,
        "a cell in another object is outside every range the call declared"
    );

    let inside = at(block("global:g"), 0);
    let outcome = same(Resource::Cell(&inside), &point(&after), &point(&entry));
    let Sameness::Unknown { why, .. } = outcome else {
        panic!("a call that may write the cell is unknown, not {outcome:?}");
    };
    assert_eq!(why.change, Change::Call { ranges });
    assert_eq!(
        why.reason,
        StopReason::NotShownSeparate(SeparationCheck::RangeDisjointness)
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
    let outcome = same(Resource::Cell(&cell), &point(&after), &point(&entry));
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
        same(Resource::Cell(&cell), &point(&after), &point(&entry)),
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

/// With one point and no second one to compare against, the tracker reports
/// the step that ended the last stretch of agreement — and reports `Same`
/// when the recorded history holds no such step.
#[test]
fn one_sided_explanation_reaches_the_beginning_of_the_history() {
    let entry = entry_memory();
    let cell = at(block("global:g"), 0);
    let explanation = explain_last_same(Resource::Cell(&cell), &point(&entry));
    assert_eq!(explanation.outcome, Sameness::Same);
    assert_eq!(explanation.there, None);

    let written = at(PointerBlock::Symbolic(Variable(78)), 0);
    let after = entry.store(written.clone(), one());
    let explanation = explain_last_same(Resource::Cell(&cell), &point(&after));
    let Some((_, stop)) = explanation.outcome.blocking_step() else {
        panic!("an unseparated store is a blocking step");
    };
    assert_eq!(stop.change, Change::Store { pointer: written });
    assert_eq!(explanation.resource, OwnedResource::Cell(cell));
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
    let explanation = explain(Resource::Cell(&cell), &point(&after), &point(&entry));
    assert_eq!(
        explanation
            .outcome
            .blocking_step()
            .map(|(at, _)| at.clone()),
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
            OwnedResource::Cell(cell.clone()),
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
