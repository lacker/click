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

int32 arena_alloc(struct arena* arena, int32 count, struct region* region) {
    int32 i;
    int32 run_length;
    int32 start;
    int32 end;

    if (count <= 0) {
        return 0;
    }
    if (count > arena->capacity) {
        return 0;
    }

    i = 0;
    run_length = 0;
    while (i < arena->capacity && run_length < count) {
        if (arena->occupied[i] == 0) {
            run_length = run_length + 1;
        } else {
            run_length = 0;
        }
        i = i + 1;
    }

    if (run_length < count) {
        return 0;
    }

    start = i - count;
    end = i;
    i = start;
    while (i < end) {
        arena->occupied[i] = 1;
        i = i + 1;
    }

    region->arena = arena;
    region->start = start;
    region->end = end;
    arena->live_regions = arena->live_regions + 1;
    return 1;
}
