# Havoc pointer- and array-typed locals at the loop head

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced with
`click verify` (exit 0 on a false postcondition).

`havoc_loop_modified_locals` (`src/kernel/loops.rs:1612-1665`) collects every
`Assign` target in the loop body through `collect_loop_modified_locals`, but
the value match at `loops.rs:1635-1643` does `CType::Int32Pointer => continue`,
`CType::UInt8Pointer => continue`, and the same for both array types. A
pointer local reassigned in the body therefore keeps its concrete pre-loop
value in the abstract loop-top state. A pure pointer-increment body has
`statement_may_write_memory == false` (`loops.rs:1667-1673`), so the memory
havoc branch never runs either, and preservation checks only invariant
propositions, never that a non-havoced local is actually loop-invariant. The
exit path returns `Normal(top_state.clone())` (`loops.rs:584-588`), so the
post-loop state inherits the stale pointer. The join abstraction in
`abstract_c_state_for_join_across_with_policy` (`src/kernel/api.rs:456`) does
havoc pointer locals to `Pointer::symbolic`; the loop path is the outlier.

The parser accepts `int32* p;` locals and `p = p + 1;` as a scalar-update
assign, so this is reachable from plain source today.

## Violated invariant

The abstract loop-top state must give a fresh, unconstrained value to every
local the loop body can modify, regardless of its type, so that the invariant
is assumed over an arbitrary iteration and the loop-exit state cannot carry a
value that is only correct for the pre-loop iteration.

## Intended regression

```c
int32 stale_ptr(int32 arr[], int32 n, int32 cap) {
    int32* p; int32 i;
    p = arr; i = 0;
    while (i < n) { i = i + 1; p = p + 1; }
    return *p;
}
```

```click
verifying "stale_ptr.c";
int32 stale_ptr(int32 arr[], int32 n, int32 cap) {
    requires 0 <= n; requires n < cap; requires 1 <= cap;
    views arr[0..cap];
    ensures result == arr[0];
} by { step(); step(); step(); step();
       loop { invariant i >= 0 and i <= n; }
       step(); simp(); }
```

Today this verifies although the function returns `arr[n]`. After the fix it
must fail, and the true postcondition `ensures result == arr[n]` must be
provable with an invariant that relates `p` to `arr` and `i` (for example
`p == arr + i` once pointer-offset invariants are expressible, or an explicit
`have`).

## Acceptance criteria

- `havoc_loop_modified_locals` gives every loop-modified pointer local a fresh
  symbolic pointer (matching the join abstraction's treatment) and every
  loop-modified array-object local a fresh block or an explicit rejection;
  no `continue` arm remains for a modifiable type.
- A kernel unit test in `src/kernel/tests/` asserts that the loop-top state
  for the regression body binds `p` to a variable distinct from the entry
  pointer.
- The mdtest above fails with a prompt, local diagnostic naming the stale
  local, and a positive mdtest proves the true postcondition.
- `scripts/check.sh` passes.

Related: [loop-heap-and-resource-frame.md](loop-heap-and-resource-frame.md)
covers the other components the same function leaves stale;
[loop-havoc-write-set.md](loop-havoc-write-set.md) covers framing loads
across memory-writing loops, which pointer-chasing loops will also need.
