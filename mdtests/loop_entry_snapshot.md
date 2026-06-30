# loop entry snapshots in invariants

This checks `at(region.entry, expr)` for a loop code region. The loop invariant
uses the value of `n` at the loop-entry visit while the loop body mutates `n`.

```c filename=loop_entry_snapshot.c
int32 drain_to_zero(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "loop_entry_snapshot.c";

int32 drain_to_zero(int32 n) {
    requires n >= 0;
    requires n <= 100;

    for loop(0) as drain {
        invariant n >= 0 by auto;
        invariant at(drain.entry, n) >= 0 by auto;
    }

    ensures returns_zero: result == 0 by auto;
}
```

```expect
pass
```
