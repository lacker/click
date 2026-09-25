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
    struct arena* arena;
    int32 allocated;

    arena_free(middle);
    arena = middle->arena;
    allocated = arena_alloc(arena, 2, reused);
    return allocated;
}
