# Iterated ownership refuses to gather while a guard is unknown

`gather` forms an iterated fact from the range its elements cover, which is
sound only when every guard of the range is known: all true, so the fact
holds every element, or all false, so it holds none. Here the occupancy map
was never written, so nothing says which cells are free, and the step is
refused. The accepted form zeroes the map first, as in
[`iterated_ownership_gather_scatter.md`](iterated_ownership_gather_scatter.md).

```c filename=iterated_ownership_rejects_gather_unknown_guards.c
void adopt(int32* data, int32* occupied, int32 capacity) {}
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

verifying "iterated_ownership_rejects_gather_unknown_guards.c";

void adopt(int32* data, int32* occupied, int32 capacity) {
    requires 0 <= capacity;
    consumes occupied[0..capacity];
    consumes data[0..capacity];
    produces arena_cells(data, occupied, capacity);
} by {
    gather(arena_cells(data, occupied, capacity));
    fold(arena_cells(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
fail: gathering needs every guard known
```
