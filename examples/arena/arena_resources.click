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

resource arena_init_result(arena: struct arena*, initialized: int32) {
    owns object(arena);
    contains arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        initialized
    );
    fact initialized == 0 or initialized == 1;
    fact initialized == 0 implies arena->data == 0;
    fact initialized == 0 implies arena->occupied == 0;
    fact initialized == 0 implies arena->capacity == 0;
    fact initialized == 0 implies arena->live_regions == 0;
    fact initialized == 1 implies arena->live_regions == 0;
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
