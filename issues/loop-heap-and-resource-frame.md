# Reconcile heap lifetime and resource state at the loop back edge

Found by the 2026-09-01 kernel audit at cb034b21. Both shapes below were
reproduced with `click verify` (exit 0 on undefined behavior).

The loop-top abstraction `havoc_loop_modified_locals`
(`src/kernel/loops.rs:1612-1665`) clones the entry `CState` and rewrites only
`state.locals` and, through `with_loop_memory_havoc`
(`src/kernel/primitives/memory_state.rs:448-468`), memory cells. It never
touches `state.resources` or `memory.heap` (live, deallocated, and pending
allocations, or the block set). `collect_loop_preservation_summary`
(`loops.rs:926-1037`) executes the body from the loop top and, on a `Normal`
path, collects only effect-check and invariant-check obligations; it never
compares the body's post-state resources or heap set to the loop top, and
`CLoopInvariantCheck` carries only a `SpecProposition`. The exit path is
`Normal(top_state.clone())` (`loops.rs:584-588`). The surface `loop` tactic
uses the same `prepare_loop_top_state` and `c_loop_preservation_contexts`
entry points (`src/kernel/api.rs:157-230`), so the proof-layer route has the
same gap.

Consequences: a block freed inside the loop is still live and owned after it;
a resource consumed inside the loop (directly or by a callee whose contract
`consumes` it) is still held at the loop top and after the loop; the stale
resource also balances the end-of-function leak check. The straight-line
equivalents are all correctly rejected.

## Violated invariant

The abstract loop-head state, and therefore the loop-exit state, must
over-approximate every reachable loop-head state in every component of
`CState`: locals, memory cells, heap lifetime state (`memory.heap`), and the
resource context. A loop body whose net effect changes heap lifetime or the
resource context must either be rejected at the back edge or have that change
restated by the invariant bundle.

## Intended regression

Heap lifetime:

```c
int32 double_free(int32* data) {
    int32 i; i = 0;
    while (i < 1) { free(data); i = i + 1; }
    free(data);
    return 0;
}
```

```click
resource allocated_int32s(data: int32*, count: int32) {
    contains allocation(data, count * 4); owns data[0..count]; fact data != 0;
}
verifying "double_free.c";
int32 double_free(int32* data) {
    requires data != 0; consumes allocated_int32s(data, 1); ensures result == 0;
} by {
    unfold(allocated_int32s(data, 1)); step(); step();
    loop { invariant 0 <= i; initialize by simp; preserve by { step(); step(); close_invariants(); } }
    execute(); simp();
}
```

A variant with `data[0] = 5; value = data[0]; free(data); return value;` after
the loop and `ensures result == 5` also verifies today.

Resource context:

```c
int32 take(int32* p) { return 0; }
int32 use_after_take(int32* p) {
    int32 i; int32 status; i = 0; status = 0;
    while (i < 1) { status = take(p); i = i + 1; }
    p[0] = 7;
    return status;
}
```

```click
verifying "take.c"; verifying "use_after_take.c";
int32 take(int32* p) { consumes p[0..1]; ensures result == 0 by auto; }
int32 use_after_take(int32* p) {
    owns p[0..1]; mutable p[0..1]; ensures p[0] == 7;
} by { step(); step(); step(); step();
       loop { invariant i >= 0; invariant i <= 1; mutable p[0..1] by frame; }
       step(); step(); frame(); simp(); }
```

An abstract-token twin (a callee that `consumes can_complete(cb)` called
inside a loop, with the caller declared `owns can_complete(cb)`) verifies
today as well. All of these must fail after the fix with a diagnostic at the
back edge naming the changed allocation or resource.

## Acceptance criteria

- Every `Normal` back-edge path is checked, by the kernel, to reach a heap
  lifetime state and resource context definitionally equal to (or entailing)
  the loop top's, or the loop top havocs those components and the invariant
  bundle must restate whatever survives. Either design is acceptable; the
  check must not be a surface-side convention.
- Loop bodies containing `HeapFree`, `HeapAllocate`, or calls whose contracts
  consume or produce resources are covered; the check must not be skipped
  when the effect-check list is empty.
- Negative kernel tests reject a body that frees a live block, a body that
  consumes an owned memory range, and a body that consumes an abstract token,
  without falling back to concrete unrolling.
- Negative mdtests for the three regressions above, plus a positive mdtest
  showing a loop that frees a block on its last iteration can still be
  verified with an invariant that states the conditional ownership.
- `scripts/check.sh` passes.

Related: `havoc_loop_modified_locals` (pointer locals are havoced since 2026-09-01) fixes
the third stale component in the same function.
