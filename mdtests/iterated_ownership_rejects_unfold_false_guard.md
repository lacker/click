# Iterated ownership refuses to take an element whose guard is false

On the occupied path `occupied[index] != 0`, so the iterated fact holds
nothing at `index`: the cell belongs to whoever claimed it. Taking it out
would mint ownership the arena does not have, so indexed `unfold` is refused. The
accepted form takes on the free path only, as in
[`iterated_ownership_allocate_one.md`](iterated_ownership_allocate_one.md).

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
