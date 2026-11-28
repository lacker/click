# a store dropped by the next store is still on the history

The write to `a[j]` may alias the cell `a[i] = 7` left behind, so it drops that
cell. What remains is an empty cell map — the same cell map function entry had.
If the two were one state, the read of `a[m]` at the end would be named by
the entry state and `result == old(a[m])` would hold by spelling, with no rule
having decided it. The C returns 7 when `i` and `m` are the same index.

The forget mark keeps the two apart. The refusal must compare distinct
states rather than treating the final read as an entry read. Its supplemental,
fact-free history explanation may stop at the later store to `a[j]`: program
reads name the actual state, not a cache projection that removed that store.

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
}
```

```expect
fail: the two sides read the same address in different memory states (`result` reads the memory recorded at `statement(2).exit`; `old(a[m])` reads the function-entry memory)
```
