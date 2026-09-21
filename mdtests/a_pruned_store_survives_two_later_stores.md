# a forgotten store is still on the history two steps later

The same shape as
[`a_pruned_store_is_not_forgotten.md`](a_pruned_store_is_not_forgotten.md) with
a third store in between, which writes `a[m]` back with the value it just read.
The store to `a[i]` is the one that may have changed the answer, and it is the
one the refusal has to name however many steps later the read happens.

```c filename=a_pruned_store_survives_two_later_stores.c
int32 read_after_three_stores(int32* a, int32 i, int32 j, int32 m) {
    a[i] = 7;
    a[j] = 0;
    a[m] = a[m];
    return a[m];
}
```

```click
verifying "a_pruned_store_survives_two_later_stores.c";

int32 read_after_three_stores(int32* a, int32 i, int32 j, int32 m) {
    owns a[0..8];
    requires 0 <= i;
    requires i < 8;
    requires 0 <= j;
    requires j < 8;
    requires 0 <= m;
    requires m < 8;
    requires m != j;
    ensures result == old(a[m]);
} by {
    execute();
    simp();
}
```

```expect
fail: the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`
```
