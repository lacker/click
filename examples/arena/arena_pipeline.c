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

int32 arena_pipeline(
    struct arena* arena,
    struct region* first,
    struct region* second,
    struct region* combined
) {
    int32 initialized;
    int32 allocated;
    int32 first_value;
    int32 second_value;
    int32 value;

    initialized = arena_init(arena, 8);
    if (initialized == 0) {
        return 0;
    }

    allocated = arena_alloc(arena, 2, first);
    if (allocated == 0) {
        arena_destroy(arena);
        return 0;
    }

    allocated = arena_alloc(arena, 2, second);
    if (allocated == 0) {
        arena_free(first);
        arena_destroy(arena);
        return 0;
    }

    arena_write(first, 0, 11);
    arena_write(second, 0, 22);
    first_value = arena_read(first, 0);
    second_value = arena_read(second, 0);
    value = first_value + second_value;

    arena_free(second);
    arena_free(first);

    allocated = arena_alloc(arena, 4, combined);
    if (allocated == 0) {
        arena_destroy(arena);
        return 0;
    }

    arena_write(combined, 3, value);
    value = arena_read(combined, 3);
    arena_free(combined);
    arena_destroy(arena);
    return value;
}
