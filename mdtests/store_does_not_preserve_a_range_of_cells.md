# a store does not preserve every cell of the range it writes into

The binder form of `store_does_not_preserve_a_symbolic_cell.md`. Under
`intro()` the item is an arbitrary index of the range, so it cannot be told
apart from the written one, and the universal is not available.

```c filename=store_does_not_preserve_a_range_of_cells.c
void mark_one(int32 a[], int32 n, int32 i) {
    a[i] = 1;
}
```

```click
verifying "store_does_not_preserve_a_range_of_cells.c";

void mark_one(int32 a[], int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    requires n <= 1073741823;
    consumes a[0..n];
    produces a[0..n];
} by {
    mark entry;
    step();
    have forall (k: int32) {
        0 <= k and k < n implies a[k] == at(entry, a[k])
    } by {
        intro();
        intro();
        simp();
    }
    execute();
    simp();
}
```

```expect
fail: `have` failed for `forall (k: int32) { ((0 <= k && k < n) => a[k] == at(entry, a[k])) }`
```
