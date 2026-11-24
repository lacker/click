# Iterated ownership still checks its guards

indexed `unfold` is a checked memory step: taking an
element whose guard is false is still refused.

```c filename=iterated_ownership_rejects_unfold_false_guard.c
void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    if (occupied[index] != 0) {
        data[index] = 7;
    }
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

verifying "iterated_ownership_rejects_unfold_false_guard.c";

void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index < capacity;
} by {
    unfold(arena_cells(data, occupied, capacity));
    if occupied[index] != 0 {
        unfold(arena_cells(data, occupied, capacity)[index]);
    } else {
        step_until(function.exit);
        fold(arena_cells(data, occupied, capacity));
        close();
    }
}
```

```expect
fail: the guard is false at this index
```
