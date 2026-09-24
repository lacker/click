# Iterated ownership: allocation protocol for one element

`claim` takes one free cell out of the arena's iterated ownership, marks it
occupied, and hands it to the caller. On the free path the proof takes the
element out while its guard `occupied[index] == 0` holds, which makes the
index a hole of the iterated fact. The C store `occupied[index] = 1` then
writes a guard cell the fact makes no claim about, and because the stored
value makes the guard false the hole closes again: the refolded
`arena_cells` owes nothing for the claimed cell, which the caller now owns
through `claimed`. On the occupied path nothing moves.

```c filename=iterated_ownership_allocate_one.c
int32 claim(int32* data, int32* occupied, int32 capacity, int32 index) {
    if (occupied[index] != 0) {
        return 0;
    }
    occupied[index] = 1;
    data[index] = 7;
    return 1;
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

verifying "iterated_ownership_allocate_one.c";

int32 claim(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    produces cell: claimed(data, index);
    requires 0 <= index;
    requires index < capacity;
    ensures cell.held == result;
} by {
    unfold(arena_cells(data, occupied, capacity));
    if occupied[index] != 0 {
        execute();
        fold(arena_cells(data, occupied, capacity));
        let cell = fold(claimed(data, index), { held: 0 });
        simp();
    } else {
        take(data[index..index + 1]);
        execute();
        fold(arena_cells(data, occupied, capacity));
        let cell = fold(claimed(data, index), { held: 1 });
        simp();
    }
}
```

```expect
pass
```
