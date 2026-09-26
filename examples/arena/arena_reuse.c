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

int32 arena_reuse(struct region* middle, struct region* reused) {
    int32 allocated;

    arena_free(middle);
    allocated = arena_alloc(middle->arena, 2, reused);
    return allocated;
}
