# A loop invariant states a viewable prefix that grows with the index

`viewable(a[0..i])` is a stated range, so its extent half — `i` read as an
element count, `0 <= i` and `i <= 1073741823` for four-byte elements — is part
of the invariant: owed at entry and at the back edge, assumed at the head. The
kernel once spelled the count bound as an unsigned comparison with a sign-bit
bias, and the condition checker looked it up only in that spelling, so the
natural invariants `0 <= i` and `i <= n`, with the contract's
`n <= 1073741823`, were refused for a bound nothing in scope wrote that way —
even beside an explicit `invariant i <= 1073741823`. Below the sign bit the
unsigned bound means exactly `0 <= i` and `i <= 1073741823`, and the checker
decides it that way, through the same order facts it reads for any signed
comparison.

```c filename=loop_invariant_states_a_growing_viewable_prefix.c
int32 any_zero(int32 *a, int32 n) {
    int32 found = 0;
    for (int32 i = 0; i < n; i++) {
        if (a[i] == 0) {
            found = 1;
        }
    }
    return found;
}
```

```click
verifying "loop_invariant_states_a_growing_viewable_prefix.c";

int32 any_zero(int32 *a, int32 n) {
    views a[0..n];
    requires 0 <= n;
    requires n <= 1073741823;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant viewable(a[0..i]);
    }
    execute();
    simp();
}
```

```expect
pass
```
