struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

void arena_destroy(struct arena* arena) {
    free(arena->occupied);
    free(arena->data);
    arena->data = 0;
    arena->occupied = 0;
    arena->capacity = 0;
    arena->live_regions = 0;
}
