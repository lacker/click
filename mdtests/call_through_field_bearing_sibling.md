# A caller applies a contract whose clauses read through a field-bearing sibling

The call-site twin of
[`arena_prefix_free_reads_region_arena.md`](arena_prefix_free_reads_region_arena.md).
`arena_release` consumes `freed: arena_prefix_region(region)` and
`before: arena_live_count(region->arena)`, and produces
`after: arena_live_count(region->arena)`. `caller` holds both instances folded
and hands them over with a binder map.

A call reads the callee's clauses as one set, exactly as the callee's entry
does. The bound instances are checked together, so `region->arena` is
addressed through the cells the folded region's unconditional, unmatched body
owns; and the produced instance's argument is read at the return through the
contract's own input instances, before the returned clauses are composed.
Nothing is unfolded in the caller.

```c filename=release.c
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

void arena_release(struct region* region) {
    struct arena* arena;

    arena = region->arena;
    arena->live_regions = arena->live_regions - 1;
}

void caller(struct region* region) {
    arena_release(region);
}
```

```click
resource arena_live_count(arena: struct arena*) {
    field live: int32;
    owns &arena->data;
    owns arena->live_regions;
    fact arena->live_regions == live;
}

resource arena_prefix_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns object(region);
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}

verifying "release.c";

void arena_release(struct region* region) {
    consumes freed: arena_prefix_region(region);
    consumes before: arena_live_count(region->arena);
    requires 1 <= before.live;
    produces object(region);
    produces region->arena->data[region->start..region->end];
    produces after: arena_live_count(region->arena);

    ensures after.live == old(before.live) - 1;
} by {
    let { live: n } = unfold(before);
    let { start: s, end: e } = unfold(freed);
    execute();
    let after = fold(arena_live_count(region->arena), { live: n - 1 });
    simp();
}

void caller(struct region* region) {
    consumes freed: arena_prefix_region(region);
    consumes before: arena_live_count(region->arena);
    requires 1 <= before.live;
    produces object(region);
    produces region->arena->data[region->start..region->end];
    produces after: arena_live_count(region->arena);
} by {
    let { after: after } = step(arena_release(region), { freed: freed, before: before });
    step();
    simp();
}
```

```expect
pass
```
