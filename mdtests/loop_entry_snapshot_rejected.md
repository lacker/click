# loop entry snapshots are stable during preservation

```c filename=loop_entry_snapshot_rejected.c
int32 c(int32 n) {
    int32 x;
    x = 0;
    while (x < n) {
        x = x + 1;
    }
    return x;
}
```

```click
verifying "loop_entry_snapshot_rejected.c";

int32 c(int32 n) {
    requires n >= 5 and n < 1000;
    ensures result <= 1;
} by {
    step();
    step();
    loop as L {
        invariant x >= 0 and x <= n;
        invariant x - 1 <= at(L.entry, x);
    }
    step();
    have at(L.entry, x) == 0 by { simp(); }
    have result - 1 <= at(L.entry, x) by { simp(); }
    have result - 1 <= 0 by {
        rewrite(at(L.entry, x) == 0);
        assumption();
    }
    have result <= 1 by { arithmetic() using { result - 1 <= 0; } }
    simp();
}
```

```expect
fail: closure body did not prove every invariant obligation
```
