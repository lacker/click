# A loop invariant states a viewable prefix that grows with the index

`viewable(a[0..i])` is a stated range, so at the loop head its extent half is
owed as `i` read as an unsigned element count: `i <=u 1073741823` for four-byte
elements. The kernel spells that bound with a sign-bit bias, and the condition
checker used to look it up only in that spelling, so the natural invariants
`0 <= i` and `i <= n`, with the contract's `n <= 1073741823`, were refused at the
loop head for a bound nothing in scope wrote that way — even beside an explicit
`invariant i <= 1073741823`. Below the sign bit the unsigned bound means exactly
`0 <= i` and `i <= 1073741823`, and the checker now decides it that way, through
the same order facts it reads for any signed comparison.

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
