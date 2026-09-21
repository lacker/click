# a store whose cell survives still stops a read of that cell

With `i != j` stated, the write to `a[j]` no longer drops the `a[i]` cell, so
nothing is forgotten and no mark is set. This is the case that was already
refused before marks existed, and it must keep being refused for the same
reason: `a[m]` may be `a[i]`.

Keeping it beside
[`a_pruned_store_is_not_forgotten.md`](a_pruned_store_is_not_forgotten.md) is
what makes that one a statement about the forget rather than about the stores.

```c filename=a_store_kept_by_a_distinctness_fact_still_stops_a_read.c
int32 read_past_a_surviving_store(int32* a, int32 i, int32 j, int32 m) {
    a[i] = 7;
    a[j] = 0;
    return a[m];
}
```

```click
verifying "a_store_kept_by_a_distinctness_fact_still_stops_a_read.c";

int32 read_past_a_surviving_store(int32* a, int32 i, int32 j, int32 m) {
    owns a[0..8];
    requires 0 <= i;
    requires i < 8;
    requires 0 <= j;
    requires j < 8;
    requires 0 <= m;
    requires m < 8;
    requires m != j;
    requires i != j;
    ensures result == old(a[m]);
} by {
    execute();
    simp();
}
```

```expect
fail: the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`
```
