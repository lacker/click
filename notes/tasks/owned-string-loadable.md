# owned-string: unfold cannot discharge loadable(data[len])

Status: open — precisely localized (coordinator probe session, 2026-07-31)
Claimed: worktree-agent-aa971f675db3276c3, 2026-07-31

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
