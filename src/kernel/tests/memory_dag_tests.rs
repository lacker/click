use super::*;

#[test]
fn reinterning_retained_memory_uses_shallow_component_identity() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut memory = CMemory::new();
            for index in 0..size {
                memory = memory.with_block(format!("shallow-memory-{size}-{index}"), 4);
            }
            let first = crate::kernel::intern_c_memory_ref(&memory);
            let (second, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::intern_c_memory_ref(&memory)
            });
            assert_eq!(first.arena_id(), second.arena_id());
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.iter().all(|(_, work)| *work == 0),
        "reinterning retained memory should not hash its contents: {samples:?}"
    );
}

// --- named-memory-states arc: the derivation DAG -------------------------
// See docs/advanced/memory-dag.md. These pin the two invariants
// the arc's safety argument rests on (advisory-only, and parent id < child
// id) plus the havoc-identity property that must hold by construction.

#[test]
fn a_store_records_the_edge_from_the_snapshot_it_wrote() {
    if skip_without_memory_dag() {
        return;
    }
    let base = CMemory::new().with_block("arg-memory", 16);
    let after = base
        .clone()
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(7)));

    let derivation = crate::kernel::intern_c_memory_ref(&after)
        .derivation()
        .expect("a store records how the snapshot was produced");
    match derivation.as_ref() {
        CMemoryDerivation::Store {
            base: recorded_base,
            pointer,
            value,
        } => {
            assert_eq!(recorded_base.as_ref(), &base);
            assert_eq!(pointer, &arc_pointer(4));
            assert_eq!(value, &CValue::Int32(Bitvector32Term::Constant(7)));
        }
        other => panic!("expected a store edge, got {other:?}"),
    }
}

#[test]
fn derivation_bases_are_strictly_older_so_the_dag_cannot_cycle() {
    if skip_without_memory_dag() {
        return;
    }
    // Storing a value and then storing it back re-interns the original
    // snapshot, which is the shortest cycle the DAG could otherwise grow.
    // First-wins recording keeps the older edge, so following `base` still
    // strictly decreases and terminates.
    let base = CMemory::new().with_block("arg-memory", 16);
    let written = base
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(1)));
    let restored = written
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(0)))
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(1)));
    assert_eq!(restored, written, "the round trip returns the same value");

    let mut node = crate::kernel::intern_c_memory_ref(&restored);
    let mut hops = 0;
    while let Some(derivation) = node.derivation() {
        let next = derivation.base().clone();
        assert!(
            next.arena_id() < node.arena_id(),
            "a derivation base must be strictly older than what it derives"
        );
        node = next;
        hops += 1;
        assert!(hops < 64, "walking derivation bases must terminate");
    }
}

#[test]
fn a_store_that_changes_nothing_records_no_edge_to_itself() {
    if skip_without_memory_dag() {
        return;
    }
    let base = CMemory::new()
        .with_block("arg-memory", 16)
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(3)));
    let again = base
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(3)));
    assert_eq!(again, base);

    let node = crate::kernel::intern_c_memory_ref(&again);
    if let Some(derivation) = node.derivation() {
        assert_ne!(
            derivation.base().arena_id(),
            node.arena_id(),
            "a snapshot must never be recorded as derived from itself"
        );
    }
}

#[test]
fn loop_havoc_is_its_own_edge_kind_and_keeps_its_marker_block() {
    if skip_without_memory_dag() {
        return;
    }
    let base = CMemory::new()
        .with_block("arg-memory", 16)
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(5)));
    let after = base
        .clone()
        .with_loop_memory_havoc(Variable(0), &BTreeSet::new());

    assert!(
        after.has_block(&"havoc:0".into()),
        "the freshness marker block must survive the arc untouched"
    );
    let derivation = crate::kernel::intern_c_memory_ref(&after)
        .derivation()
        .expect("loop havoc records how the snapshot was produced");
    match derivation.as_ref() {
        CMemoryDerivation::LoopHavoc {
            base: recorded_base,
            variable,
        } => {
            assert_eq!(recorded_base.as_ref(), &base);
            assert_eq!(*variable, Variable(0));
        }
        other => panic!("expected a loop-havoc edge, got {other:?}"),
    }
}

#[test]
fn derivations_carry_a_load_across_a_distinct_store_but_not_across_havoc() {
    // The first consumer of the DAG: load preservation answered from the
    // recorded history rather than from effect facts. A store to a provably
    // distinct cell is crossable; a loop havoc between the same endpoints is
    // not, because it has no write set to be disjoint from.
    //
    // Only the positive direction is the DAG's to add. The havoc refusals
    // are soundness properties that must hold with the arc switched off too,
    // so they run under both settings.
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);

    if !skip_without_memory_dag() {
        // A call havoc changes the block set (it adds its marker block), so
        // the snapshot-diff matcher refuses to look at the cells at all. The
        // recorded edge carries the call's mutable ranges, so the walk can
        // still cross it for a pointer provably outside them. This is the
        // case the DAG answers and value bridging cannot.
        let called = base.clone().with_call_memory_havoc(
            Variable(3),
            &[memory_range(arc_pointer(8), 0, 8)],
            &Assumptions::new(),
        );
        assert!(
            !memories_match_for_pointer_load_under_assumptions(
                &base,
                &called,
                &read,
                &Assumptions::new()
            ),
            "the snapshot-diff matcher is expected not to cross the marker block"
        );
        assert!(
            c_memory_load_is_unchanged(&base, &called, &read, &Assumptions::new()),
            "a call that may only write a disjoint range preserves the load"
        );
    }

    let havoced = base
        .clone()
        .with_loop_memory_havoc(Variable(7), &BTreeSet::new());
    assert!(
        !c_memory_load_is_unchanged(&base, &havoced, &read, &Assumptions::new()),
        "loop havoc must never be crossed without explicit frame evidence"
    );

    let havoced_then_stored = havoced
        .clone()
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(9)));
    assert!(
        !c_memory_load_is_unchanged(&base, &havoced_then_stored, &read, &Assumptions::new()),
        "a crossable store must not smuggle a walk past an intervening havoc"
    );
}

/// Stage 4: the DAG-guided cell lookup answers load equality for snapshots
/// that are *siblings*, which the stage-2 walk cannot do because it only ever
/// asks whether one snapshot is reachable from the other.
///
/// Two calls, each havocking a range disjoint from the loaded cell, produce
/// two snapshots neither of which derives from the other. Value bridging
/// refuses them outright — each carries its own `call-havoc:N` marker block,
/// so the block sets differ and the snapshot matcher stops before looking at
/// any cell. Resolving both against the write history lands them on one
/// common ancestor, and the loads are equal with no snapshot comparison.
#[test]
fn sibling_snapshots_resolve_one_cell_to_a_common_ancestor() {
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let load_in = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(read.clone()),
        )
    };
    let call_havoc = |variable| {
        base.clone().with_call_memory_havoc(
            Variable(variable),
            &[memory_range(arc_pointer(8), 0, 8)],
            &Assumptions::new(),
        )
    };
    let (left, right) = (call_havoc(3), call_havoc(4));

    assert!(
        !memories_match_for_pointer_load_under_assumptions(
            &left,
            &right,
            &read,
            &Assumptions::new()
        ),
        "the two marker blocks are expected to stop the snapshot matcher"
    );
    assert_eq!(
        Assumptions::new().memory_loads_proven_equal(&load_in(&left), &load_in(&right)),
        !skip_without_memory_dag(),
        "the common-ancestor lookup is exactly what the DAG adds here"
    );

    // Soundness, and so asserted in both modes: an intervening loop havoc has
    // no write set, so no walk may resolve through one.
    let havoced = left
        .clone()
        .with_loop_memory_havoc(Variable(9), &BTreeSet::new());
    assert!(
        !Assumptions::new().memory_loads_proven_equal(&load_in(&left), &load_in(&havoced)),
        "loop havoc must stop the cell lookup"
    );
}

/// The owned-string loadable shape: the permission fact and its bound facts
/// spell `len` as a load at contract
/// entry, while the index the goal extracts spells it at a later snapshot
/// separated by a block declaration, stores, and a cell-forgetting prune —
/// exactly the edges (`BlockDeclared`, `CellsForgotten`) that used to leave
/// the two spellings in disjoint DAG components. The loadable prover's
/// extended bridging connects them; everywhere outside that prover the new
/// edges must stay invisible (pinned by the frame-evidence test above and
/// the byte-identical replay of the certified corpus).
#[test]
fn loadable_bound_check_bridges_len_spellings_across_block_and_prune_edges() {
    if skip_without_memory_dag() {
        return;
    }
    let entry = CMemory::new().with_block("arg-memory", 64);
    let len_pointer = arc_pointer(0);
    let len_at_entry = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&entry),
        Box::new(len_pointer.clone()),
    );

    // The recorded facts: the buffer permission and both `len` bounds, all
    // spelled at entry.
    let assumptions = Assumptions::new()
        // Same-block permissions that cannot cover `buffer[len]`. These used
        // to trigger costly general equality searches before the matching
        // symbolic range was considered.
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(0),
            bytes: Bitvector32Term::Constant(4),
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(8),
            bytes: Bitvector32Term::Constant(4),
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(12),
            bytes: Bitvector32Term::Constant(4),
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(16),
            bytes: Bitvector32Term::Constant(32),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), len_at_entry.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(len_at_entry, Bitvector32Term::Constant(8)),
            true,
        );

    // The later snapshot: a local declared, a distinct cell written, and the
    // write-path prune that forgets it again. Its `len` load is a different
    // spelling of the same cell.
    let later = entry
        .clone()
        .with_block("local:i", 4)
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(9)))
        .store(arc_pointer(8), CValue::Int32(Bitvector32Term::Constant(2)))
        .without_possible_aliasing_cells(&arc_pointer(4), &assumptions);
    let len_at_later = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&later),
        Box::new(len_pointer),
    );

    // loadable(buffer[len]) with `len` spelled at the later snapshot.
    let goal_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(16)),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(len_at_later),
                byte_width: 4,
            }),
        ),
    };
    assert!(
        assumptions.proves_memory_loadable(&later, &goal_base, &Bitvector32Term::Constant(4)),
        "the loadable bound check must connect the two len spellings along \
         the recorded block-declaration and cell-forgetting edges"
    );
}

#[test]
fn a_store_to_the_loaded_cell_is_not_crossable() {
    // A soundness property, so it must hold with the arc switched off too.
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let stored = base
        .clone()
        .store(read.clone(), CValue::Int32(Bitvector32Term::Constant(9)));

    assert!(
        !c_memory_load_is_unchanged(&base, &stored, &read, &Assumptions::new()),
        "the walk must refuse the very cell that was written"
    );
}

/// The premise-availability path matches two spellings of one fact whose load
/// atoms carry different memory snapshots. The match is decided by proof, not
/// by ignoring the snapshots: an unframed call havoc between the two snapshots
/// blocks it, and an effect summary that frames the loaded pointer restores it.
#[test]
fn conditions_equal_modulo_proven_snapshots_needs_frame_evidence() {
    let before = CMemory::new()
        .with_block("arg-memory", 8)
        .with_block("call-havoc:0", 0);
    let after = before.clone().with_block("call-havoc:1", 0);
    let loaded = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let elsewhere = Pointer {
        block: "other-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let condition = |memory: &CMemory| {
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(77)),
            Bitvector32Term::add(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory.clone()),
                    Box::new(loaded.clone()),
                ),
                Bitvector32Term::Constant(1),
            ),
        )
    };

    // Same snapshot: the two spellings are literally one condition.
    assert!(
        Assumptions::new()
            .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&before))
    );

    // A call havoc stands between the snapshots and nothing frames the load,
    // so the later spelling is a different fact, not another spelling.
    assert!(
        !Assumptions::new()
            .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after)),
        "an unframed call havoc must not be matched away"
    );

    // With an effect summary whose mutable range misses the loaded pointer,
    // the two snapshots provably agree there and the spellings match.
    let framed = Assumptions::new().assume_proposition(Proposition::CMemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            elsewhere,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });
    assert!(
        framed.conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after)),
        "a framed load should match across the effect"
    );

    // Framing never relaxes the structure: a different condition stays
    // different however well the snapshots are framed.
    let other = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(78)),
        Bitvector32Term::add(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after.clone()),
                Box::new(loaded.clone()),
            ),
            Bitvector32Term::Constant(1),
        ),
    );
    assert!(!framed.conditions_equal_modulo_proven_snapshots(&condition(&before), &other));
}
