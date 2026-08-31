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

int32 arena_read(struct region* region, int32 index) {
    struct arena* arena;

    arena = region->arena;
    return arena->data[region->start + index];
}
