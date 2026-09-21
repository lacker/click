# a write to another object does not restore a forgotten store

A field write to an unrelated object follows the pruning store, so the snapshot
the read happens at is not the one the forget produced. The store to `a[i]` is
still the step that may have changed `a[m]`, and it is what the refusal names.

```c filename=a_pruned_store_beside_a_field_write_is_not_forgotten.c
struct Node {
    int32 head;
    int32 tail;
};

int32 read_after_a_field_write(struct Node* n, int32* a, int32 i, int32 j, int32 m) {
    a[i] = 7;
    a[j] = 0;
    n->head = 1;
    return a[m];
}
```

```click
verifying "a_pruned_store_beside_a_field_write_is_not_forgotten.c";

int32 read_after_a_field_write(struct Node* n, int32* a, int32 i, int32 j, int32 m) {
    owns a[0..8];
    owns n[0..1];
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
fail: result == old(a[m])
```
