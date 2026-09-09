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
    ensures returns_zero: result == 0;
} by {
    loop as drain {
        invariant n >= 0;
        invariant n <= at(drain.entry, n);
        preserve by {
            have 0 <= n - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }
            }
            have n <= at(drain.entry, n) by { assumption(); }
            have n - 1 <= at(drain.entry, n) by {
                arithmetic() using { n >= 0; n <= at(drain.entry, n); }
            }
            step();
            close_invariants by {
                both { arithmetic() using { 0 <= n; } }
                and { simp(); }
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
