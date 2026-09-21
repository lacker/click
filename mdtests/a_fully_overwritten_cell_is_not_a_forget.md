# a cell this store overwrites is stale, not forgotten

A store drops the cells it may alias and the cells whose every byte it writes.
Only the first loses knowledge: the second is replaced by the value about to be
stored, so the result still says everything about the state it describes. Were
the second marked as a forget too, every straight-line sequence of writes to one
cell would mint a fresh chain of snapshots for no reason.

```c filename=a_fully_overwritten_cell_is_not_a_forget.c
int32 write_twice(int32* a, int32 i) {
    a[i] = 7;
    a[i] = 3;
    return a[i];
}
```

```click
verifying "a_fully_overwritten_cell_is_not_a_forget.c";

int32 write_twice(int32* a, int32 i) {
    owns a[0..8];
    requires 0 <= i;
    requires i < 8;
    ensures result == 3;
} by {
    execute();
    simp();
}
```

```expect
pass
```
