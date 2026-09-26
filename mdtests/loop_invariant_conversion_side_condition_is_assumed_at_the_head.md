# An invariant's conversion side condition is assumed at the head

`to_integer(i + 1)` converts a C `int32` expression, and the conversion is
defined only where `i + 1` does not overflow. That condition is a side
condition of the invariant's lowering, like the extent half of a stated range,
and it is ordinary invariant content: entry and every back edge owe it with the
invariant, and the head, the body and the exit assume it.

Nothing else here bounds `i` below `2147483647` at the exit, where the guard is
false, so the `ensures` follows only from the assumed side condition. The head
used to demand it as a missing prerequisite instead.

```c filename=loop_invariant_conversion_side_condition_is_assumed_at_the_head.c
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
verifying "loop_invariant_conversion_side_condition_is_assumed_at_the_head.c";

int32 walk(int32 n) {
    requires 0 <= n;
    requires n < 2147483647;
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
            have i <= n by { simp(); }
            have i < 2147483647 by { arithmetic() using { i <= n; n < 2147483647; } }
            have defined(i + 1) by {
                apply(int32_increment_below_max_is_defined(i)) using { i < 2147483647; }
            }
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
