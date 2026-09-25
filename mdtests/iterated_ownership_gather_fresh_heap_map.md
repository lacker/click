# Iterated ownership: gather over a freshly allocated guard map

The C loop initializes an occupancy map. Its quantified value invariant lets
`gather` decide the logical guard for every index and rearrange the owned
resources. Gathering does not execute a C read or publish initialization
facts. A subsequent C load still needs independent validity evidence.

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
