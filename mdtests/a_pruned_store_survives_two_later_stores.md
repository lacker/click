# a forgotten store is still on the history two steps later

The same shape as
[`a_pruned_store_is_not_forgotten.md`](a_pruned_store_is_not_forgotten.md) with
a third store in between, which writes `a[m]` back with the value it just read.
The store to `a[i]` may have changed the answer. The final read must still be
distinct from the entry read, even after the value is read and stored again.
The supplemental, fact-free history explanation need not cross `a[j]`.

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
}
```

```expect
fail: the two sides read the same address in different memory states (`result` reads the memory recorded at `statement(2).entry`; `old(a[m])` reads the function-entry memory)
```
