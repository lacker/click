# Iterated ownership refuses element ranges that overlap across indices

Every index of an iterated clause owns its own element range, and the fact
is only a separating conjunction when no two indices share a cell. With
`data[k..k + 2]`, index `k` and index `k + 1` would both own `data[k + 1]`, so
the declaration is refused and the diagnostic names the stride that would
keep the elements apart. The accepted form is
[`iterated_ownership_declaration.md`](iterated_ownership_declaration.md).

```c filename=iterated_ownership_rejects_overlapping_elements.c
void keep(int32* data, int32* occupied, int32 capacity) {}
```

```click
resource pair_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 2];
        }
    }
}

verifying "iterated_ownership_rejects_overlapping_elements.c";

void keep(int32* data, int32* occupied, int32 capacity) {
    owns pair_cells(data, occupied, capacity);
} by {
    execute();
    simp();
}
```

```expect
fail: element ranges of different indices overlap
```
