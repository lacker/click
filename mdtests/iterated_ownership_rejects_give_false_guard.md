# Iterated ownership refuses to give back an element whose guard is false

`give` moves an element into the iterated fact, which only holds elements
whose guard is true. Here the C code marks the cell occupied instead of
clearing it, so after the store the guard `occupied[index] == 0` is false and
the element cannot go back: the fact would claim a cell its guard says it
does not hold. The accepted form clears the flag first, as in
[`iterated_ownership_release_one.md`](iterated_ownership_release_one.md).

```c filename=iterated_ownership_rejects_give_false_guard.c
void release(int32* data, int32* occupied, int32 capacity, int32 index) {
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

resource claimed(data: int32*, index: int32) {
    field held: int32;
    if held == 1 {
        owns data[index..index + 1];
    }
}

verifying "iterated_ownership_rejects_give_false_guard.c";

void release(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    consumes cell: claimed(data, index);
    requires 0 <= index;
    requires index < capacity;
    requires cell.held == 1;
} by {
    unfold(arena_cells(data, occupied, capacity));
    unfold(cell);
    step();
    give(data[index..index + 1]);
    fold(arena_cells(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
fail: the guard is false at this index
```
