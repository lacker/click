struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

int32 arena_init(struct arena* arena, int32 capacity) {
    int32* data;
    int32* occupied;
    int32 i;

    arena->data = 0;
    arena->occupied = 0;
    arena->capacity = 0;
    arena->live_regions = 0;

    if (capacity <= 0) {
        return 0;
    }
    if (capacity > 536870911) {
        return 0;
    }

    data = malloc(capacity * 4);
    if (data == 0) {
        return 0;
    }

    occupied = malloc(capacity * 4);
    if (occupied == 0) {
        free(data);
        return 0;
    }

    i = 0;
    while (i < capacity) {
        occupied[i] = 0;
        i = i + 1;
    }

    arena->data = data;
    arena->occupied = occupied;
    arena->capacity = capacity;
    return 1;
}
