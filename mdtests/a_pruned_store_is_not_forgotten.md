# a store dropped by the next store is still on the history

The write to `a[j]` may alias the cell `a[i] = 7` left behind, so it drops that
cell. What remains is an empty cell map — the same cell map function entry had.
If the two were one snapshot, the read of `a[m]` at the end would be named by
the entry state and `result == old(a[m])` would hold by spelling, with no rule
having decided it. The C returns 7 when `i` and `m` are the same index.

The forget mark is what keeps the two apart, so the read stops at the store to
`a[i]` and the refusal names the premise that would let it past.

```c filename=a_pruned_store_is_not_forgotten.c
int32 read_after_a_pruned_store(int32* a, int32 i, int32 j, int32 m) {
    a[i] = 7;
    a[j] = 0;
    return a[m];
}
```

```click
verifying "a_pruned_store_is_not_forgotten.c";

int32 read_after_a_pruned_store(int32* a, int32 i, int32 j, int32 m) {
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
