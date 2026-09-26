# a read separated from both stores over a variable extent is framed

The positive twin of
[`a_pruned_store_over_a_variable_extent_is_not_forgotten.md`](a_pruned_store_over_a_variable_extent_is_not_forgotten.md).
Refusing to compare cell maps over different forget marks must not cost the
proof that does hold: with `m` stated distinct from both written indexes, the
recorded history crosses the store to `a[j]`, the forget, and the store to
`a[i]`, and reaches function entry.

```c filename=a_pruned_store_over_a_variable_extent_with_a_separated_read_is_framed.c
int32 read_after_a_pruned_store(int32* a, int32 n, int32 i, int32 j, int32 m) {
    a[i] = 7;
    a[j] = 0;
    return a[m];
}
```

```click
verifying "a_pruned_store_over_a_variable_extent_with_a_separated_read_is_framed.c";

int32 read_after_a_pruned_store(int32* a, int32 n, int32 i, int32 j, int32 m) {
    owns a[0..n];
    requires 0 <= i;
    requires i < n;
    requires 0 <= j;
    requires j < n;
    requires 0 <= m;
    requires m < n;
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
