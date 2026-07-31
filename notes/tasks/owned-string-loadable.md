# owned-string: unfold cannot discharge loadable(data[len])

Status: loadable gap CLOSED (2026-07-31, branch
worktree-agent-aa971f675db3276c3); example still quarantined — next
frontier is the have's postcondition derivation replay, plus a
runtime finding (whole example takes minutes). See "Resolution" below.
Claimed:

Example `owned-string` (quarantined in tests/examples.rs) fails in
~2.6 s: in `owned_string_push`, the `terminated_at` smart-have's
unfold cannot discharge `loadable(data[len])`. A permission-plumbing
question, not load equality — independent of the containment-prover
critical path.

Dead end (recorded, do not re-attempt): feeding `replay.effect_facts`
into planning — stores are execution facts, not effect summaries.

Open question the agent may escalate: if the fix wants to extend the
"predicate that reads memory implies readability" ruling to a NEW
position (predicate bodies in have/unfold position), that is the
owner's call.

Repro:
```
./target/debug/click-verify examples/owned-string/owned_string.click
```

Done when: owned-string verifies and de-quarantines.

## Localization (coordinator, 2026-07-31 — probes stripped, no code landed)

The failing check, exactly: during unfold-planning's symbolic contract
load of `data[len]`, `proves(&required)` on
`CMemoryLoadable(bytes=4)` fails. The chain:

- `proves`' CMemoryLoadable arm (assumptions.rs ~3428) calls ONLY
  `proves_memory_loadable` — note the richer transport +
  `loadable_covered_by_fact` + simplify arms exist only in
  `proves_atomic_without_search` (~3757). Separate observation worth
  its own look: is that split intentional?
- `proves_memory_loadable` sees all 4 CMemoryLoadable facts; every
  candidate reaches `pointer_in_range_for_memory_resolution` and
  fails there (4/4).
- Inside `bitvector_index_in_range_shallow`: the UPPER bound
  (`len < cap`) PROVES. The LOWER bound (`0 <= len`) FAILS: the
  recorded exact fact spells `len` as a load at contract-entry memory
  `{}`, while the extracted index spells it at a later snapshot
  (blocks `{local:index}` + cells over arg-memory). Verbatim exact
  lookup misses on spelling alone.

**Dead end measured:** pushing `canonicalize_atomic_loads(index)` as
an extra index candidate in
`pointer_in_range_for_memory_resolution_with_depth` — does NOT fix
it; canonicalization cannot drop the snapshot's cells (that would
need the distinctness reasoning in question). Reverted.

**Direction:** connect the two `len` spellings deterministically via
the memory DAG (`atomic_loads_equal_along_memory_derivations` /
`memory_dag_cell_source`, src/kernel/api.rs) inside the shallow bound
check's exact lookups — e.g., for a MemoryLoad index, also try
spellings reachable along derivation edges, or compare against fact
spellings with the DAG equality instead of `==`. Advisory and
deterministic; keep it depth-gated. Repro is 2.6 s.

## Resolution (2026-07-31, commit "Bridge loadable bound checks…")

The DAG could NOT connect the two spellings as landed: the later
snapshot's chain broke at TWO edge-less producers, not one.

1. Block declaration (`with_block`) — the punted fourth edge kind.
2. The write path's cell-forgetting prune
   (`without_possible_aliasing_cells` at eval.rs write_c_lvalue_paths):
   every store first prunes possibly-aliasing cells, and the pruned
   base interned with no edge. This is why execution states kept
   re-rooting the DAG at every buffer store.

What landed (all in the kernel, no surface change):

- `CMemoryDerivation::BlockDeclared` (never for havoc marker blocks)
  and `CMemoryDerivation::CellsForgotten` (write-path prune only —
  the `without_cell` case-split prune is branch-conditional and must
  never record an edge).
- Extended DAG bridging, scoped via `with_extended_dag_bridging` to
  `Assumptions::proves_memory_loadable` ONLY: cross the two new edge
  kinds; `Store`-hop distinctness upgraded to
  `pointers_proven_distinct_for_memory_resolution` under
  `with_isolated_memory_resolution_fuel` (the buffer-store hops need
  the recorded `CResourceSeparate` ranges); stored-value pinning in
  `atomic_loads_equal_along_memory_derivations` (a load-caching store's
  recorded value IS the older spelling verbatim), memoized keyed on
  (assumptions memo id, derivation generation, arena ids, pointer);
  DAG-equality matching inside `has_exact_order_path`; and an
  increment-overflow discharge from any strict exact upper bound
  (`len < cap` pins `len < INT_MAX`, so `len+1` cannot overflow).
- One nested cell-lookup level (`CELL_LOOKUP_DEPTH` cap 2): a hop's
  range certificate may itself need a single DAG hop to match its
  base spelling. Depth-1 answers are never memoized.

Why the scoping is load-bearing (measured, do not widen casually):
enabling the power globally broke later functions of the SAME example
two different ways — shared-fuel drain shifted the canonical Return
spelling (replay kept cells the certificate dropped), and stronger
distinctness changed simp case-split structure
(pop_preserves_first: "planned simp context premise is not an
available source fact"). Scoped to the loadable prover, both gate
passes are green in both DAG modes.

New kernel test:
`loadable_bound_check_bridges_len_spellings_across_block_and_prune_edges`
(src/kernel/tests.rs) — builds the two spellings across
block/store/prune edges and asserts `proves_memory_loadable`
concludes.

Gates (run twice, second after probe cleanup): `cargo nextest run
--lib --bins` 530/530; `cargo test --test mdtests` 7.3 s; `cargo test
--test examples` 8.5 s; `CLICK_DISABLE_MEMORY_DAG=1 cargo test --test
mdtests` 6.7 s.

## Remaining (example still quarantined)

With the loadable discharged, `owned_string_push` tactic 7 advances
and fails at: "`have` failed: expressible path facts do not replay
the postcondition derivation" — a different, un-diagnosed frontier
(the have's postcondition derivation replay, not permission
plumbing). ALSO a runtime finding: the full example run now takes
minutes (was 2.6 s to first failure), because the extended-bridging
walks run inside every loadable check of every function; the memo is
generation-invalidated and execution's load-caching stores bump the
generation constantly. Any successor should profile before extending.
