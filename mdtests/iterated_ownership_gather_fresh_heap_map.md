# Iterated ownership: gather over a freshly allocated guard map

`with_fresh_map` allocates an occupancy map, zeroes it in a loop, forms the
iterated ownership fact over the caller's data with `gather`, dissolves it
again with `scatter`, and frees the map. This is the shape of an arena's
initialization: the guard cells are heap cells that were never written
before the loop, so a guard cell has a value only through the loop's
quantified fact.

`gather` decides every guard at once by instantiating the quantified fact at
an arbitrary index. It used to read the guard cell first, as a C load, and a
never-written heap cell has no value until some fact establishes one, so the
read failed as an uninitialized read before the fact was consulted. The
quantified fact is now instantiated at the cell's load and the cell read
again under it; the read still decides initialization.

```c filename=iterated_ownership_gather_fresh_heap_map.c
void with_fresh_map(int32* data, int32 capacity) {
    int32* occupied;
    int32 i;

    occupied = malloc(capacity * 4);
    if (occupied == 0) {
        return;
    }
    i = 0;
    while (i < capacity) {
        occupied[i] = 0;
        i = i + 1;
    }
    free(occupied);
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

verifying "iterated_ownership_gather_fresh_heap_map.c";

void with_fresh_map(int32* data, int32 capacity) {
    requires 1 <= capacity;
    requires capacity <= 536870911;
    owns data[0..capacity];
} by {
    step();
    step();
    step();
    branch {
        then {
            execute();
            simp();
        }
        else {}
    }
    step();
    loop {
        decreases capacity - i;
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];
    }
    have i == capacity by simp;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        rewrite(capacity == i);
        assumption();
    }
    gather(arena_cells(data, occupied, capacity));
    scatter(arena_cells(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
pass
```
