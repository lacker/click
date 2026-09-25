# A free contract names the arena through a field-bearing region

`arena_release` takes only the region descriptor, so its contract has to name
the arena as `region->arena`. The live-region resource `arena_prefix_region`
owns that descriptor and carries plain fields, the interval endpoints `start`
and `end`. Its body is unconditional and unmatched, so while the contract's
clauses are evaluated the folded instance publishes the cells it owns as read
authority for the sibling clauses: `object(region)` makes `region->arena`
readable, and `arena_live_count(region->arena)` evaluates. This is the same
publication a folded field-free composite makes
(`mdtests/contract_owns_through_composite_field.md`) and a decided match arm
makes.

The publication is read authority only. The region stays folded at entry, and
the proof moves its cells into the state with an explicit `unfold`, exactly as
it moves the live count's. The live count is unfolded first because it owns
`&arena->data`, the cell the region's range `region->arena->data[start..end]`
loads its base from. The shape is the one the arena example's `arena_free`
needed in its earlier prefix model, and the per-cell `arena_free` names
`arena_state(region->arena)` beside `arena_region(region)` the same way; the
C here keeps only the live-count decrement so the fixture isolates contract
addressing from the occupancy loop.

```c filename=arena_prefix_free_reads_region_arena.c
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

verifying "arena_prefix_free_reads_region_arena.c";

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
```

```expect
pass
```
