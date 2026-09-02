# Prove a loop invariant that relates a havoced pointer local to the index

Found on 2026-09-01 while closing the loop-havoc-pointer-locals issue.

The loop head now havocs a pointer local the body reassigns
(`havoc_loop_modified_locals`, `src/kernel/loops.rs`), so a pointer-advancing
loop needs an invariant relating the pointer to the loop index. Writing that
invariant as `p == arr + i` currently fails before any proof step runs:

```text
execution proof traversal at statement(4) is missing prerequisite (loop has
neither a safe exit nor a safe iteration):
Equal(Condition(Constant(false)), Condition(Constant(true)))
```

The invariant lowers to a contradictory constant at the loop head. It is not
`blocks_proven_distinct` (`src/kernel/primitives/term_operations.rs:706`),
which does not separate a `PointerBlock::Symbolic` block from an argument
block; where the constant false comes from has not been traced. Without this,
the cursor idiom `while (p < end) { ...; p = p + 1; }` and index-tracking
pointer loops have no provable invariant, and the examples route every
traversal through recursion.

## Violated invariant

A pointer equality between a havoced pointer local and an expression over
the loop index must lower to a symbolic condition that the invariant machinery
can assume at the loop head and re-establish at the back edge, exactly like an
int32 equality.

## Intended regression

```c
int32 last_element(int32 arr[], int32 n, int32 cap) {
    int32* p; int32 i;
    p = arr; i = 0;
    while (i < n) { i = i + 1; p = p + 1; }
    return *p;
}
```

```click
verifying "last_element.c";
int32 last_element(int32 arr[], int32 n, int32 cap) {
    requires 0 <= n; requires n < cap; requires 1 <= cap;
    views arr[0..cap];
    ensures result == arr[n];
} by {
    step(); step(); step(); step();
    loop {
        invariant i >= 0 and i <= n;
        invariant p == arr + i;
    }
    step(); simp();
}
```

This must verify. `mdtests/c_loop_havoc_rejects_stale_pointer_local.md` is
the matching negative fixture and must keep failing.

## Acceptance criteria

- The lowering of `p == arr + i` at a loop head with a symbolic `p` produces
  a `PointerEqual` (or same-block offset) condition, not a constant.
- The invariant is assumable at the loop top, preserved across
  `p = p + 1; i = i + 1;`, and usable after the loop to resolve `*p`.
- The mdtest above passes; `scripts/check.sh` passes.

Related: [loop-havoc-write-set.md](loop-havoc-write-set.md) for framing
loads across such loops;
[pointer-comparison-and-subtraction.md](pointer-comparison-and-subtraction.md)
for `p < end`.
