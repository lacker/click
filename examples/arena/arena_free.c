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

void arena_free(struct region* region) {
    struct arena* arena;
    int32 i;

    arena = region->arena;
    i = region->start;
    while (i < region->end) {
        arena->occupied[i] = 0;
        i = i + 1;
    }
    arena->live_regions = arena->live_regions - 1;
}
