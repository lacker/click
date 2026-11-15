// Scaling tests of `src/kernel/quantified_frame.rs` (module `conjunct_elimination_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Carrying `defined(p[0])` out of `other and defined(p[0])` across one
/// disjoint store costs the same beside 16, 64 or 256 unrelated stores made
/// before the source state and as many unrelated facts in the querying
/// context: conjunction elimination reads only the source's conjunction
/// spine, and the definedness leaf, decided here by the kernel's typed-read
/// no-write walk standing in for the single-fact route, reads only the steps
/// between its two states.
#[test]
fn conjunct_elimination_is_flat_against_unrelated_history_and_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: "conjunct-frame".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let unrelated = Pointer {
        block: "conjunct-frame-unrelated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut costs = Vec::new();
    for size in [16u32, 64, 256] {
        let mut before = Memory::new()
            .with_block("conjunct-frame", 16)
            .with_block("conjunct-frame-unrelated", size);
        for index in 0..size {
            before = before.store(
                unrelated.offset_by_bytes(index),
                crate::kernel::uint8(index % 251),
            );
        }
        let after = before
            .clone()
            .store(base.offset_by_bytes(8), crate::kernel::uint8(0));
        let assumptions = (0..size).fold(PureFactContext::new(), |context, index| {
            context.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Variable(Variable(50_000 + u64::from(index))),
                true,
            ))
        });
        let defined = |memory: &Memory| Proposition::MemoryReadDefined {
            memory: memory.clone(),
            pointer: base.clone(),
            value_type: ProgramType::UInt8,
        };
        // Built outside the measurement: interning a state is paid by
        // whoever builds it, not by the frame.
        let other = Proposition::ConditionIs(ConditionTerm::Variable(Variable(49_999)), true);
        let source = Proposition::And(Box::new(other), Box::new(defined(&before)));
        let target = defined(&after);
        let leaf =
            |from: &Proposition, to: &Proposition, context: &PureFactContext| match (from, to) {
                (
                    Proposition::MemoryReadDefined {
                        memory: before,
                        pointer,
                        value_type,
                    },
                    Proposition::MemoryReadDefined { memory: after, .. },
                ) => crate::kernel::memory_provenance::typed_read_has_same_memory_source(
                    before,
                    after,
                    pointer,
                    value_type.byte_width(),
                    context,
                ),
                _ => false,
            };
        let facts = ProofFacts::default();
        let same = |context: PureFactContext| context;
        let variables = BTreeSet::new();
        let (carried, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame_quantified_transport(
                &source,
                &target,
                &facts,
                &assumptions,
                &assumptions,
                &leaf,
                &same,
                &variables,
            )
        });
        assert_eq!(carried, Ok(()));
        costs.push(work);
    }
    eprintln!("conjunct elimination work by size: {costs:?}");
    assert!(
        costs.windows(2).all(|pair| pair[0] == pair[1]),
        "conjunct elimination work: {costs:?}"
    );
}

/// Measure a cold query after constructing and interning its input states.
fn load_equality_work(earlier: u32, between: u32, written: bool) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: "load-frame".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let unrelated = Pointer {
        block: "load-frame-other".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut before = Memory::new()
        .with_block("load-frame", between + 8)
        .with_block("load-frame-other", earlier);
    if written {
        before = before.store(base.clone(), crate::kernel::uint8(7u32));
    }
    for index in 0..earlier {
        before = before.store(
            unrelated.offset_by_bytes(index),
            crate::kernel::uint8(index % 251),
        );
    }
    let mut after = before.clone();
    for index in 0..between {
        after = after.store(base.offset_by_bytes(8 + index), crate::kernel::uint8(0u32));
    }
    let bi = crate::kernel::intern_memory_ref(&before);
    let ai = crate::kernel::intern_memory_ref(&after);
    let load = |m: &SharedMemory| {
        MachineTerm::MemoryLoad(m.clone(), Box::new(base.clone()), LoadKind::UInt8)
    };
    let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::explicit_atomic_equality_from_memory_derivations(
            &load(&bi),
            &load(&ai),
            &PureFactContext::new(),
        )
    });
    assert!(equal);
    work
}

/// A first load-equality query pays for the state delta, never the stores
/// before both endpoints, even if the queried cell was written before them.
#[test]
fn load_equality_ignores_history_before_both_states() {
    for written in [false, true] {
        let costs = [16u32, 64, 256].map(|size| load_equality_work(size, 1, written));
        eprintln!("load equality work, written={written}: {costs:?}");
        assert!(
            costs.windows(2).all(|p| p[0] == p[1]),
            "load equality work: {costs:?}"
        );
    }
}

/// The bounded walk still visits the intervening steps; it cannot accept
/// states by ignoring their delta or by using a warm answer.
#[test]
fn load_equality_work_tracks_the_state_delta() {
    let costs = [1u32, 4, 16].map(|between| load_equality_work(256, between, true));
    eprintln!("load equality work by state delta: {costs:?}");
    assert!(
        costs.windows(2).all(|p| p[0] < p[1] && p[1] <= 4 * p[0]),
        "load equality work: {costs:?}"
    );
}
