# Iterated ownership refuses to take an element whose guard is unknown

indexed `unfold` moves one element out of the iterated fact, which requires the fact
to hold it: the index must be in range and its guard must be known true.
Here nothing says whether `occupied[index]` is zero, so the fact may or may
not hold `data[index]`, and the step is refused. The accepted form decides
the guard first, as in
[`iterated_ownership_allocate_one.md`](iterated_ownership_allocate_one.md).

```c filename=iterated_ownership_rejects_unfold_unknown_guard.c
void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
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

verifying "iterated_ownership_rejects_unfold_unknown_guard.c";

void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index < capacity;
} by {
    unfold(arena_cells(data, occupied, capacity));
    unfold(arena_cells(data, occupied, capacity)[index]);
    step_until(function.exit);
    fold(arena_cells(data, occupied, capacity)[index]);
    fold(arena_cells(data, occupied, capacity));
    close();
}
```

```expect
fail: the guard at this index is not known to hold
```
