# a read separated from both stores still reads the entry value

The positive twin of
[`a_pruned_store_is_not_forgotten.md`](a_pruned_store_is_not_forgotten.md).
Marking the snapshot the dropped cell came from must not cost the proof that
does hold: with `m` stated distinct from both written indexes, the walk crosses
the store to `a[j]`, crosses the forget, crosses the store to `a[i]`, and
reaches function entry.

```c filename=a_pruned_store_with_a_separated_read_is_framed.c
int32 read_beside_a_pruned_store(int32* a, int32 i, int32 j, int32 m) {
    a[i] = 7;
    a[j] = 0;
    return a[m];
}
```

```click
verifying "a_pruned_store_with_a_separated_read_is_framed.c";

int32 read_beside_a_pruned_store(int32* a, int32 i, int32 j, int32 m) {
    owns a[0..8];
    requires 0 <= i;
    requires i < 8;
    requires 0 <= j;
    requires j < 8;
    requires 0 <= m;
    requires m < 8;
    requires m != i;
    requires m != j;
    ensures result == old(a[m]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
