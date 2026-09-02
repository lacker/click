# Give the memory DAG's loop-havoc edge a write set

Found by the 2026-09-01 kernel audit at cb034b21 and narrowed after a
citation check: loop framing exists today, but only outside the memory DAG.

`CMemoryDerivation::CallHavoc` carries `mutable_ranges`
(`src/kernel/primitives.rs:1110`), and the DAG crossing rules let a load
transport across it with disjointness evidence. `CMemoryDerivation::LoopHavoc`
carries only a `variable` (`primitives.rs:1099`) and is never crossed:
`src/kernel/memory_provenance.rs:731` reports it non-crossable and `:1736`
returns `Unwritten` unconditionally.

Loop framing works through a different mechanism. `with_loop_memory_havoc`
(`src/kernel/primitives/memory_state.rs:462-463`) drops every non-preserved
cell, but its caller `prepare_loop_top_state` (`src/kernel/loops.rs:1118-1143`)
copies back every entry-state cell that
`ranges_proven_disjoint_from_pointer` places outside the whole-loop
`mutable_ranges` of the `CMemoryEffectSummary` that
`collect_whole_loop_effect_summaries` (`loops.rs:1047-1096`) builds from the
loop's `mutable ... by frame` clauses; that summary is assumed at the loop
head, checked at every back edge, and consumed by `frame(loop(0))` in ensures
proofs. `mdtests/shifted_loop_effect_preserves_prefix.md` and
`mdtests/frame_loop_region_preserves_symbolic_index.md` verify
`p[0] == old(p[0])` and `p[n] == old(p[n])` across loops that write the rest
of the buffer, and `docs/concepts/proof-workflow.md:569-574` documents it.

What is not framed: a cell absent from entry memory (never loaded before the
loop) is not copied back, and no DAG provenance crosses the loop, so a
post-loop load of such a cell cannot be related to its pre-loop value except
through the surface-consumed summary. The two mechanisms also differ from
the call case, where provenance is the single source of truth, which
matters as [double-execution.md](double-execution.md) moves certification
onto retained typed evidence.

## Violated invariant

A loop with a verified `mutable` footprint should have the same DAG framing
power as a verified call with the same footprint: a load proved disjoint from
every range transports across the `LoopHavoc` edge through provenance,
whether or not the cell was materialized at loop entry.

## Intended regression

Kernel unit test in `src/kernel/tests/memory_dag_tests.rs`: after a
`LoopHavoc` recorded with ranges `[p, p + n)`, `memory_dag_cell` for a load
at `q` proved disjoint from that range must not return
`MemoryDagCell::Unwritten` at the `LoopHavoc` hop, while a load inside the
range still does. An mdtest in which a post-loop straight-line load of a cell
that was never loaded before the loop (so it is absent from entry memory and
not copied back) is proved equal to its `old(...)` value without
`frame(loop(0))`. The two existing mdtests named above are the baseline and
must keep passing.

## Acceptance criteria

- `LoopHavoc` carries the checked mutable ranges of the loop's verified effect
  summary, and the crossing rules in `memory_provenance.rs` mirror
  `CallHavoc`; loops without a verified footprint keep today's conservative
  behavior.
- The copy-back in `prepare_loop_top_state` either becomes redundant with
  provenance or is documented as a materialization optimization that cannot
  disagree with it.
- The tests above pass; `scripts/check.sh` passes.

Related: `havoc_loop_modified_locals` (pointer locals are havoced since 2026-09-01).
