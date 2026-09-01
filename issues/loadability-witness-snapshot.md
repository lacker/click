# Check the witnessing load's snapshot before certifying loadability

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced with
`click verify` (exit 0) on a postcondition that reads a freed heap block.

`condition_fact_mentions_load_of`
(`src/kernel/api/contract_certification.rs:375`) discards the memory snapshot
of the witnessing load (it matches `MemoryLoad(_, ptr)` and drops the memory
of `registered_load_for_variable`). Its consumers destructure the goal as
`CMemoryLoadable { base, bytes, .. }`, so a fact about `load(M0, p)` certifies
loadability of `p` in any later snapshot `M1`. The exploitable consumer is the
`_ =>` arm at `contract_certification.rs:620` of
`quantified_int32_fact_certifies_loadable_cell`, the general 4-byte cell
prover reached from `PureFactContext::proves_memory_loadable_inner` and
`proves_memory_loadable_for_memory_resolution`
(`src/kernel/assumptions/memory_reasoning.rs:206`, `:364`). The sibling
`CMemoryLoadable` arm at `:601` performs a `memory_range_still_available`
check; this arm does not. Spec-level loads (`src/kernel/spec.rs:1095-1135`)
have no deallocation tombstone check and emit exactly the `CMemoryLoadable`
obligation this prover discharges. C-body loads remain protected by
`read_c_lvalue_paths`.

A related weakness: for `ExternalArgument` blocks
`memory_range_still_available` itself is satisfied across `free` because
`free_heap_block` keeps external blocks, so `ensures data[0] == data[0]` after
`free(data)` also verifies.

## Violated invariant

A condition fact constraining `load(M0, p)` witnesses loadability of `p` only
in `M0` or in a snapshot where `p`'s block is still available. A contract may
not assert a defined read of memory that the function freed.

## Intended regression

```c
int32 zero_one(int32 p[]) { p[0] = 0; return 0; }
int32* uaf_local(int32 fallback[], int32 j) {
    int32* p; int32 r;
    p = malloc(4); if (p == 0) { return fallback; }
    r = zero_one(p); free(p); return p;
}
```

```click
verifying "zero_one.c"; verifying "uaf_local.c";
int32 zero_one(int32 p[]) { owns p[0..1]; mutable p[0..1];
    ensures forall (k: int32) { 0 <= k and k < 1 implies p[k] == 0 }; } by { execute(); frame(); simp(); }
int32* uaf_local(int32 fallback[], int32 j) {
    requires 0 <= j; requires j < 1; views fallback[0..1];
    ensures result[j] == result[j];
} by { execute(); simp(); }
```

Today this exits 0. Controls that already fail with "missing pure fact:
loadable(...)" and must keep failing: inline the store instead of calling the
helper; replace the helper's `forall` with plain `ensures p[0] == 0`; read
`result[0]` instead of `result[j]`. After the fix the sidecar must fail with
the same loadability diagnostic. A second regression: `ensures data[0] ==
data[0]` on a function that frees its `int32 data[]` argument must fail.

## Acceptance criteria

- `condition_fact_mentions_load_of` receives the load's memory (from
  `MemoryLoad(memory, _)` and from the registered load) and every consumer
  requires `memory_range_still_available(load_memory, goal_memory, base)` or a
  canonical/effect equality before accepting the witness.
- `memory_range_still_available` treats a freed `ExternalArgument` block as
  unavailable, or `free` on an external block records a tombstone the
  transport predicate honors.
- Kernel unit tests for the quantified-witness case and the external-block
  case; negative mdtests for both regressions; `scripts/check.sh` passes.
