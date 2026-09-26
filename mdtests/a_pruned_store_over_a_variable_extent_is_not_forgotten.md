# a store dropped by the next store is not forgotten over a variable extent

The variable-extent companion of
[`a_pruned_store_is_not_forgotten.md`](a_pruned_store_is_not_forgotten.md),
and a false theorem until the snapshot comparisons read the forget mark.

With `owns a[0..n]` nothing seeds the entry cell map, so it is empty. The store
to `a[i]` records one cell, and the store to `a[j]` forgets it, because the two
indexes may be equal. The forget mark keeps that state apart from function
entry, and the read of `a[m]` is named at it. What the comparison then asked
was which *cells* the two snapshots disagree on — and they agree on every
cell, since neither holds one. An empty difference was read as "nothing
differs", so `result == old(a[m])` held with no rule having looked at the
store to `a[i]`. The C returns 7 when `i` and `m` are equal.

A cell map is knowledge about the state its forget mark names. Two maps over
different marks are compared by the recorded history, which stops at the
store to `a[i]` and names the premise that would let the read past it.

```c filename=a_pruned_store_over_a_variable_extent_is_not_forgotten.c
int32 read_after_a_pruned_store(int32* a, int32 n, int32 i, int32 j, int32 m) {
    a[i] = 7;
    a[j] = 0;
    return a[m];
}
```

```click
verifying "a_pruned_store_over_a_variable_extent_is_not_forgotten.c";

int32 read_after_a_pruned_store(int32* a, int32 n, int32 i, int32 j, int32 m) {
    owns a[0..n];
    requires 0 <= i;
    requires i < n;
    requires 0 <= j;
    requires j < n;
    requires 0 <= m;
    requires m < n;
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
