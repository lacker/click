# a loop `owns` clause preserves a symbolic index

This checks that a loop's `owns` clause certifies a memory-preservation goal
with no framing tactic. The loop owns `p[0..n]`, so `p[n]` keeps its
entry-state value even though the preserved index is symbolic, and the closing
`simp` certifies `p[n] == old(p[n])` from the loop's owned footprint alone.

```c filename=loop_owns_preserves_symbolic_index.c
int32 loop_owns_preserves_symbolic_index(int32 p[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_owns_preserves_symbolic_index.c";

int32 loop_owns_preserves_symbolic_index(int32 p[], int32 n) {
    requires n >= 0;
    requires n <= 100;
    requires loadable(p[0..n + 1]);
    consumes p[0..n + 1];
    ensures preserved: p[n] == old(p[n]);
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
        owns p[0..n];
        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
