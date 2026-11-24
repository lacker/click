# Iterated ownership refuses a store to an element that was not taken out

The iterated fact holds `data[index]` while its guard is true, but holding it
there grants no access: a C store needs the element as owned memory, which
only indexed `unfold` provides. The accepted form is
[`iterated_ownership_allocate_one.md`](iterated_ownership_allocate_one.md).

```c filename=iterated_ownership_rejects_store_with_closed_slot.c
void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    if (occupied[index] != 0) {
        return;
    }
    data[index] = 7;
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

verifying "iterated_ownership_rejects_store_with_closed_slot.c";

void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index < capacity;
} by {
    unfold(arena_cells(data, occupied, capacity));
    if occupied[index] != 0 {
        step_until(function.exit);
        fold(arena_cells(data, occupied, capacity));
        close();
    } else {
        step_until(function.exit);
        fold(arena_cells(data, occupied, capacity));
        close();
    }
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
