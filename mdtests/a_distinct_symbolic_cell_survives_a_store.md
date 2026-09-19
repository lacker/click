# a store does preserve a cell stated distinct from the one it writes

The companion of `store_does_not_preserve_a_symbolic_cell.md`: the frame
transport is what carries the entry read to the post-store snapshot, and the
premise it needs is the distinctness of the two indexes. A spec read leaves its
load unresolved where it cannot decide the alias, so this premise, and not the
shape of the load, is what makes the transport apply.

```c filename=a_distinct_symbolic_cell_survives_a_store.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "a_distinct_symbolic_cell_survives_a_store.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    requires loadable(a[0..n]);
    consumes a[0..n];
    produces a[0..n];
} by {
    mark entry;
    step();
    have at(entry, a[m]) == at(entry, a[m]) by { normalize(); }
    transport(
        at(entry, a[m]) == at(entry, a[m]),
        at(entry, a[m]) == a[m]
    ) using {
        at(entry, a[m]) == at(entry, a[m]);
        m != i;
    };
    execute();
    simp();
}
```

```expect
pass
```
