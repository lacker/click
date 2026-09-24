# Iterated ownership: free protocol for one element

`release` hands one claimed cell back to the arena by clearing its occupancy
flag. The caller owns the cell outright through `claimed`, so the arena's
iterated fact cannot hold it (owned memory is a partition): the store
`occupied[index] = 0` writes a guard cell at which the fact claims nothing,
and the store rule opens a hole there. The stored value makes the guard
true, so the hole stays open until `give` moves the element back in; only
then does `arena_cells` fold again. The allocation direction is
[`iterated_ownership_allocate_one.md`](iterated_ownership_allocate_one.md).

```c filename=iterated_ownership_release_one.c
void release(int32* data, int32* occupied, int32 capacity, int32 index) {
    occupied[index] = 0;
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

verifying "iterated_ownership_release_one.c";

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
pass
```
