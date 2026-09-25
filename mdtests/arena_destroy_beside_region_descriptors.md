# Destroying an arena while the caller keeps region descriptors

`examples/arena`'s `arena_pipeline` ends every path in `arena_destroy(arena)`
while it still owns its region descriptors. This is that call in isolation,
with the `arena_destroy` contract of the arena's earlier prefix model and the
lifecycle resources of `examples/arena/arena_resources.click`: the caller
lends `arena_empty(arena)`, which owns both backing arrays and their
allocation authority, and keeps `object(first)` and `object(second)`.

`arena_destroy` sets `arena->data` and `arena->occupied` to null, so the
allocations it frees can only be named through the values those fields had
at the call's entry, which is where the call rule reads what the caller lent.
There, the lent arena owns every byte of both backing arrays, so the owned
descriptors the caller kept are disjoint from both freed allocations by the
ownership partition (`call_retires_allocation_beside_unrelated_owner.md`).

```c filename=arena_destroy.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

struct region {
    struct arena* arena;
    int32 start;
    int32 end;
};

void arena_destroy(struct arena* arena) {
    free(arena->occupied);
    free(arena->data);
    arena->data = 0;
    arena->occupied = 0;
    arena->capacity = 0;
    arena->live_regions = 0;
}

void arena_teardown(
    struct arena* arena,
    struct region* first,
    struct region* second
) {
    arena_destroy(arena);
}
```

```click
resource arena_initialized_storage(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        contains allocation(data, capacity * 4);
        contains allocation(occupied, capacity * 4);
        fact 1 <= capacity;
        fact capacity <= 536870911;
    }
}

resource arena_initialized_access(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        owns data[0..capacity];
        owns occupied[0..capacity];
    }
}

resource arena_empty(arena: struct arena*) {
    owns object(arena);
    contains arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    );
    contains arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    );
    fact arena->live_regions == 0;
}

verifying "arena_destroy.c";

void arena_destroy(struct arena* arena) {
    consumes arena_empty(arena);
    produces object(arena);

    ensures arena->data == 0;
    ensures arena->occupied == 0;
    ensures arena->capacity == 0;
    ensures arena->live_regions == 0;
} by {
    unfold(arena_empty(arena));
    unfold(arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    unfold(arena_initialized_access(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    ));
    execute();
    simp();
}

void arena_teardown(
    struct arena* arena,
    struct region* first,
    struct region* second
) {
    consumes arena_empty(arena);
    produces object(arena);
    owns object(first);
    owns object(second);
} by {
    execute();
    simp();
}
```

```expect
pass
```
