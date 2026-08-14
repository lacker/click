# Canonical load jump launders havoc markers

`canonical_memory_for_pointer_load_with_depth`
(`src/kernel/reasoning/memory_resolution.rs`) canonicalizes a load's memory
operand. Its block-retain deliberately keeps `havoc:`/`call-havoc:` marker
blocks — they are the signal that a mutation event stands between two
snapshots, and the `with_block` soundness-trap comment plus
`conditions_equal_modulo_proven_snapshots_needs_frame_evidence` pin that a
havoc must never be matched away without frame evidence.

The **materialization-source jump** bypasses that protection: when every
same-block cell is a materialization cell (`load(source, own-pointer)`)
with a common canonical source, the function *replaces the whole memory
with the source*, and the original memory's havoc markers are silently
discarded. The surviving cells witness only that *they* are unchanged
since the source; they say nothing about the loaded pointer, which may sit
inside a havoc's mutable ranges while its own cell was dropped by
retention.

Consequence: `c_memory_load_is_unchanged`'s canonical-equality shortcut
(`canonical(before, p) == canonical(after, p)`) treats a load as unchanged
across a havoc that explicitly listed the loaded pointer as mutable — a
stale fact can be transported across the mutation with no frame evidence.
The same conflation reaches every consumer of the canonical form
(`equality_graph_term_key`, `normalize_direct_atomic_memory_loads`, the
premise-availability bridge).

## Reproduction (fails on master, 2026-08-14)

Add to `src/kernel/tests/memory_dag_tests.rs`:

```rust
#[test]
fn sibling_materialization_cells_must_not_launder_a_havoc() {
    let pristine = CMemory::new().with_block("arg-memory", 16);
    let loaded = arc_pointer(0);
    let sibling = arc_pointer(4);
    let materialized = pristine
        .clone()
        .store(sibling.clone(), pristine.symbolic_int32_load(&sibling));
    let havocked = materialized.clone().with_call_memory_havoc(
        Variable(9000),
        &[CMemoryRange::new(
            loaded.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
        &PureFactContext::new(),
    );

    assert!(
        !c_memory_load_is_unchanged(
            &materialized,
            &havocked,
            &loaded,
            &PureFactContext::new()
        ),
        "a havoc of the loaded pointer must not be laundered by sibling \
         materialization cells jumping to their common source"
    );
}
```

The havoc's mutable range covers `loaded`; the sibling cell survives
retention; the jump maps both memories' canonical forms to the pristine
source and the shortcut answers "unchanged".

## The fix, and what it exposes

The one-hunk fix is to re-add the original memory's marker blocks after
the jump (union), so a jumped canonical form still differs from one whose
history lacks the havoc:

```rust
let jumped = common_materialization_source.is_some();
let mut canonical = common_materialization_source.unwrap_or_else(|| memory.clone());
if jumped {
    let markers = memory
        .blocks
        .iter()
        .filter(|(block, _)| block.starts_with("havoc:") || block.starts_with("call-havoc:"))
        .map(|(block, size)| (block.clone(), size.clone()))
        .collect::<Vec<_>>();
    let blocks = std::sync::Arc::make_mut(&mut canonical.blocks);
    for (block, size) in markers {
        blocks.entry(block).or_insert(size);
    }
}
```

With the fix, the regression and the pinned frame-evidence test pass and
the unit suite is 965/965 — but the **examples gate goes red**:
`input-cursor`'s `input_cursor_shared_pipeline.contract` tactic 11 stops
finding a premise. That proof was transporting a fact across a call havoc
through the laundered canonical identity; the transport instance is very
likely *sound in context* (the loaded pointer framed by the recorded
effect summaries), but with markers preserved the two spellings differ and
the transport must be *proven* — and the premise-availability bridge
currently cannot (the same bridge gaps traced in
`indexed-resource-algebra-avoids-pairwise-context-work.md`: the snapshot
comparison's block-set prefilter, and per-cell alias evidence that the
provers do produce but the comparator never consumes).

So this fix and the lazy-separation close-out share one completion
criterion: the premise bridge must decide marker-differing spellings by
bounded proof (frame the loaded pointer across the marker delta using the
recorded effect summaries) instead of by spelling coincidence.

Measured convergence (2026-08-14, prototype `debf29f2`): with the fix
applied on the lazy-separation prototype, `bounded-pool`'s
`pool_pipeline` premise replays and the function verifies in 1.1s — the
marker union aligns the block sets of the pristine-jumped candidate and
the live required spelling, so the snapshot comparison finally consumes
the carriers' per-cell distinctness answers. The prototype's examples
frontier moves to `pool_transfer_pipeline` tactic 3, a different failure
class (`step` used an assumption-derived theorem premise without a
replayable derivation). The prototype unit suite stays 964/964 under the
fix.

## Acceptance criteria

- The regression above is in `memory_dag_tests.rs` and passes.
- The marker-union fix (or a stricter jump guard) lands in
  `canonical_memory_for_pointer_load_with_depth`; jumps never erase
  markers.
- The premise-availability bridge proves the sound transports the fix
  invalidates: `input-cursor` verifies unchanged, and the full gate is
  green with the fix in place.
- The mechanism is documented in `docs/advanced/memory-dag.md` next to the
  existing havoc-identity material.
