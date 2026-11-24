# loop entry states in invariants

This checks `at(region.entry, expr)` for a loop code region. The loop invariant
uses the value of `n` at the loop-entry visit while the loop body mutates `n`.

```c filename=loop_entry_state.c
int32 drain_to_zero(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "loop_entry_state.c";

int32 drain_to_zero(int32 n) {
    requires n >= 0;
    requires n <= 100;
    ensures returns_zero: result == 0;
} by {
    loop drain {
        decreases n;
        invariant n >= 0;
        invariant n <= at(drain.entry, n);
        maintain by {
            have 0 <= to_integer(n - 1);
            have n <= at(drain.entry, n) by close();
            have to_integer(n - 1) <= to_integer(at(drain.entry, n)) by {
                close() using { n >= 0; n <= at(drain.entry, n); };
            }
            step();
        }
    }
    step();
    close();
}
```

```expect
pass
```
