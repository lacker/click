# An arena region cannot be freed twice

`arena_prefix_region` is the live-region resource of the symbolic arena
allocation in `examples/arena/arena_pipeline.click`: the descriptor
object and the exact data interval `[start, end)` it names. A free consumes
that instance. The caller owns one instance, so the first call takes it and
the second call has no instance to hand over: the double free is refused at
the second call, where the named binder `allocated` is no longer owned.

```c filename=arena_prefix_region_double_free_free.c
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

void arena_free(struct arena* arena, struct region* region) {
}
```

```c filename=arena_prefix_region_double_free.c
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

void free_twice(struct arena* arena, struct region* region) {
    arena_free(arena, region);
    arena_free(arena, region);
}
```

```click
resource arena_prefix_region(
    arena: struct arena*,
    region: struct region*
) {
    field start: int32;
    field end: int32;
    owns object(region);
    owns arena->data[start..end];
    fact region->arena == arena;
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}

verifying "arena_prefix_region_double_free_free.c";
verifying "arena_prefix_region_double_free.c";

void arena_free(struct arena* arena, struct region* region) {
    consumes allocated: arena_prefix_region(arena, region);
}

void free_twice(struct arena* arena, struct region* region) {
    consumes allocated: arena_prefix_region(arena, region);
} by {
    step(arena_free(arena, region), { allocated: allocated });
    step(arena_free(arena, region), { allocated: allocated });
    execute();
    simp();
}
```

```expect
fail: resource proof argument is not owned
```
