# a store does not preserve a cell whose index it cannot be told apart from

A specification read denotes the value its own state holds, so a read after
this store is a load from the post-store state and a read before it is a
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
    owns a[0..n];
    ensures a[m] == old(a[m]);
}
```

```expect
fail: unclosed goal: a[m] == old(a[m]); the two sides read the same address in different memory states (`a[m]` reads the memory recorded at `region(1).exit`; `old(a[m])` reads the function-entry memory); `a[m]` may have changed since function entry: the store to `a[i]` may have written it. If `m` and `i` differ, state `m != i`.
```
