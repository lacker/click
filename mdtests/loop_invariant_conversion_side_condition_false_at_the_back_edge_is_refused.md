# An invariant's conversion side condition that fails at the back edge is refused there

The back edge owes an invariant's side conditions with the invariant, here
that `i + 1` does not overflow in `to_integer(i + 1)`. Nothing bounds `n`
below `2147483647`, so after `i = i + 1` the new `i` may be `2147483647` and
the side condition is not established at the back edge. Were it assumed at the
head without being owed there, the false `ensures defined(result + 1)` would
follow at the exit for `n == 2147483647`.

```c filename=loop_invariant_conversion_side_condition_false_at_the_back_edge_is_refused.c
int32 walk(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_invariant_conversion_side_condition_false_at_the_back_edge_is_refused.c";

int32 walk(int32 n) {
    requires 0 <= n;
    ensures defined(result + 1);
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant to_integer(i + 1) == to_integer(i + 1);
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: `defined((i + 1))` remained open
```
