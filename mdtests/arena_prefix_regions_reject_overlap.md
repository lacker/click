# Two live arena regions cannot overlap

Each `arena_prefix_region` owns its descriptor and the data interval
`[start, end)` it names, so two live regions own disjoint intervals by
construction. `carve_overlapping` describes `first` as `[0, 2)` and `second`
as `[1, 3)` inside one owned interval `[0, 4)`. The fold of `second` takes
`[1, 3)`; the fold of `first` then needs `[0, 2)`, whose cell 1 `second`
already owns, and is refused. Carving `[0, 2)` and `[2, 4)` instead verifies.

```c filename=arena_prefix_regions_reject_overlap.c
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

void carve_overlapping(struct arena* arena, struct region* first, struct region* second) {
    first->arena = arena;
    first->start = 0;
    first->end = 2;
    second->arena = arena;
    second->start = 1;
    second->end = 3;
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

verifying "arena_prefix_regions_reject_overlap.c";

void carve_overlapping(struct arena* arena, struct region* first, struct region* second) {
    owns &arena->data;
    consumes arena->data[0..4];
    consumes object(first);
    consumes object(second);
    requires separate(memory(object(arena)), memory(arena->data[0..4]));
    produces a: arena_prefix_region(arena, first);
    produces b: arena_prefix_region(arena, second);
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    let b = fold(arena_prefix_region(arena, second), { start: 1, end: 3 });
    let a = fold(arena_prefix_region(arena, first), { start: 0, end: 2 });
    simp();
}
```

```expect
fail: fold requires ownership of the complete instance body
```
