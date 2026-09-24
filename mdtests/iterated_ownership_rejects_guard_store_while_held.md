# Iterated ownership refuses a guard store while the fact holds the element

The guard is read against the current cells, so storing to `occupied[index]`
changes which elements the iterated fact holds. On the free path the fact
holds `data[index]`; marking the cell occupied without taking the element
out first would silently drop that cell from the arena, so the store is
refused. The accepted form takes the element first, as in
[`iterated_ownership_allocate_one.md`](iterated_ownership_allocate_one.md).

```c filename=iterated_ownership_rejects_guard_store_while_held.c
void mark(int32* data, int32* occupied, int32 capacity, int32 index) {
    if (occupied[index] != 0) {
        return;
    }
    occupied[index] = 1;
}
```

```click
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "iterated_ownership_rejects_guard_store_while_held.c";

void mark(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index < capacity;
} by {
    unfold(arena_cells(data, occupied, capacity));
    if occupied[index] != 0 {
        execute();
        fold(arena_cells(data, occupied, capacity));
        simp();
    } else {
        execute();
        fold(arena_cells(data, occupied, capacity));
        simp();
    }
}
```

```expect
fail: the guard holds at this index, so the fact still holds its element
```
