# Frontier: a free contract cannot name the arena through a field-bearing region

This fixture pins an open contract-lowering gap met while giving the fixed
`examples/arena/arena_free.c` a contract over the symbolic prefix resources of
`examples/arena/arena_symbolic_alloc.click`.

`arena_free` takes only the region descriptor, so its contract has to name the
arena as `region->arena`. The live-region resource owns that descriptor. When
the resource carries plain fields (here the interval endpoints `start` and
`end`), its folded cells do not become read authority for sibling clauses at
contract entry, so `arena_prefix_state(region->arena)` cannot be evaluated and
the contract is refused before any proof runs.

The same read is accepted when the owning resource has no fields:
`mdtests/contract_owns_through_composite_field.md` evaluates a sibling clause
through a cell a folded field-free composite owns, and a decided match arm
publishes its cells the same way. The intended behavior is that an
unconditional, unmatched field-bearing body publishes its cells as read
authority exactly as those two forms do; ownership would still move only on
an explicit `unfold`. When that lands, this fixture should become a passing
contract (with its proof) and the arena free should use it.

```c filename=arena_prefix_free_reads_region_arena_frontier.c
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
}
```

```click
resource arena_live_count(arena: struct arena*) {
    field live: int32;
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

verifying "arena_prefix_free_reads_region_arena_frontier.c";

void arena_free(struct region* region) {
    consumes freed: arena_prefix_region(region);
    consumes before: arena_live_count(region->arena);
}
```

```expect
fail: could not evaluate `region->arena` while checking `owns arena_live_count(region->arena)`
```
