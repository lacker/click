# a store does not preserve a cell whose index it cannot be told apart from

A specification read denotes the value its own snapshot holds, so a read after
this store is a load from the post-store snapshot and a read before it is a
load from the entry one. With nothing saying `m != i`, they are two different
values, and no route may identify them. The same read with `m != i` stated is
`a_distinct_symbolic_cell_survives_a_store.md`.

```c filename=store_does_not_preserve_a_symbolic_cell.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "store_does_not_preserve_a_symbolic_cell.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires n <= 1073741823;
    consumes a[0..n];
    produces a[0..n];
    ensures a[m] == old(a[m]);
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal: a[m] == old(a[m]); the two sides read the same address in different memory snapshots (`a[m]` reads the outcome state, `old(a[m])` reads function entry); `a[m]` at the outcome state and `a[m]` at function entry may be different reads: the store to `a[i]` in between may have written it, and `a[i]` is not shown separate from `a[m]`
```
