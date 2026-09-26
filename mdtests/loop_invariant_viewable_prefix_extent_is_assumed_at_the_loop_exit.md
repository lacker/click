# A viewable prefix's extent is assumed at the loop exit

`viewable(a[0..i])` states that `a[0..i]` is a valid byte extent, `0 <= i` and
`i <= 1073741823`, beside the viewability of those bytes. Like every other part
of an invariant it is proved at entry and at each back edge, and assumed
wherever the invariant is: at the head, in the body and at the exit.

This loop keeps no `i <= n` invariant. Inside the body the guard `i < n` and
the `views` clause's `n <= 1073741823` bound `i`, so the head used to discharge
the extent there; on the exit path the guard is false, and the exit was refused
because it could not re-derive the same extent it was assuming the invariant
with. The back edge still narrows `a[0..n]` to the new prefix from `i <= n`,
which the guard supplies and one `have` states.

```c filename=loop_invariant_viewable_prefix_extent_is_assumed_at_the_loop_exit.c
int32 walk(int32 *a, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_invariant_viewable_prefix_extent_is_assumed_at_the_loop_exit.c";

int32 walk(int32 *a, int32 n) {
    views a[0..n];
    requires 0 <= n;
    ensures result >= 0;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant viewable(a[0..i]);
        preserve by {
            step();
            have i <= n by { simp(); }
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
