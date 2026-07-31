# `apply_loop_summary` reports the frontier it was applied at

`apply_loop_summary(loop(N))` is a simple tactic that only applies at that
loop's entry. Applied anywhere else it must name the loop it was asked for
and the statement the replay frontier actually sits on, rather than stepping
a frontier that has no loop to summarize.

```c filename=sum_to.c
int32 sum_to(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "sum_to.c";

int32 sum_to(int32 n) {
    requires n >= 0 and n <= 4;

    for loop(0) {
        invariant i >= 0;
    }

    ensures nonneg: result >= 0 by {
        execute_rest();
        apply_loop_summary(loop(0));
        simp();
    }
}
```

```expect
fail: `apply_loop_summary(loop(0))` is not at that loop's entry
```
