# A free contract names the arena through a field-bearing region

`arena_release` takes only the region descriptor, so its contract has to name
the arena as `region->arena`. The live-region resource `arena_prefix_region`
owns that descriptor and carries plain fields, the interval endpoints `start`
and `end`. Its body is unconditional and unmatched, so while the contract's
clauses are evaluated the folded instance publishes the cells it owns as read
authority for the sibling clauses: `*region` makes `region->arena`
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
    owns arena->data;
    owns arena->live_regions;
    fact arena->live_regions == live;
}

resource arena_prefix_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns *region;
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
    produces *region;
    produces region->arena->data[region->start..region->end];
    produces after: arena_live_count(region->arena);

    ensures after.live == old(before.live) - 1;
} by {
    let { live: n } = unfold(before);
    let { start: s, end: e } = unfold(freed);
    have separate(memory(*region), memory(region->arena->live_regions));
    have region->arena->data == old(region->arena->data);
    have defined(region->arena) by { close(); }
    mark before_store;
    step();
    have separate(statement(0).footprint, memory(region->arena)) by {
        close() using { };
    }
    have at(statement(0).exit, defined(region->arena)) by {
        preserve(memory(region->arena), statement(0));
    }
    have region->arena == at(before_store, region->arena) by {
        preserve(memory(region->arena), statement(0));
    }
    have separate(memory((&arena)[0..1]), memory(region->arena->data));
    have separate(statement(0).footprint, memory(region->arena->data)) by {
        close() using { separate(memory((&arena)[0..1]), memory(region->arena->data)); };
    }
    have region->arena->data == at(before_store, region->arena->data) by {
        preserve(memory(region->arena->data), statement(0));
    }
    mark after_declare;
    step();
    have separate(statement(1).footprint, memory(region->arena)) by {
        close() using { };
    }
    have at(statement(1).exit, defined(region->arena)) by {
        preserve(memory(region->arena), statement(1));
    }
    have region->arena == at(after_declare, region->arena) by {
        preserve(memory(region->arena), statement(1));
    }
    have separate(memory((&arena)[0..1]), memory(region->arena->data));
    have separate(statement(1).footprint, memory(region->arena->data)) by {
        close() using { separate(memory((&arena)[0..1]), memory(region->arena->data)); };
    }
    have region->arena->data == at(after_declare, region->arena->data) by {
        preserve(memory(region->arena->data), statement(1));
    }
    have region->arena == at(before_store, region->arena) by {
        rewrite(region->arena, at(after_declare, region->arena));
        close();
    }
    mark after_assignment;
    have arena == at(after_assignment, region->arena);
    have separate(memory(at(after_assignment, &arena->live_regions)[0]), memory((&arena->data)[0..1]));
    have separate(memory(at(after_assignment, &arena->live_regions)[0]), memory(at(after_assignment, &region->arena->data)[0])) by {
        rewrite(at(after_assignment, region->arena), arena);
        close();
    }
    have separate(memory(arena->live_regions), memory(region->arena));
    step();
    have separate(statement(2).footprint, memory(region->arena)) by {
        close() using { separate(memory(arena->live_regions), memory(region->arena)); };
    }
    have at(statement(2).exit, defined(region->arena)) by {
        preserve(memory(region->arena), statement(2));
    }
    have region->arena == at(after_assignment, region->arena) by {
        preserve(memory(region->arena), statement(2));
    }
    have separate(statement(2).footprint, memory(at(after_assignment, &region->arena->data)[0])) by {
        close() using {
            separate(memory(at(after_assignment, &arena->live_regions)[0]), memory(at(after_assignment, &region->arena->data)[0]));
        };
    }
    have load<int32*>(at(after_assignment, &region->arena->data)) == at(after_assignment, region->arena->data) by {
        preserve(memory(at(after_assignment, &region->arena->data)[0]), statement(2));
    }
    have region->arena->data == load<int32*>(at(after_assignment, &region->arena->data)) by {
        rewrite(region->arena, at(after_assignment, region->arena));
        close();
    }
    have region->arena->data == at(after_assignment, region->arena->data) by {
        rewrite(region->arena->data, load<int32*>(at(after_assignment, &region->arena->data)));
        close();
    }
    have region->arena == at(before_store, region->arena) by {
        rewrite(region->arena, at(after_assignment, region->arena));
        close();
    }
    step_until(function.exit);
    have defined(region->arena) by { close(); }
    have region->start == s by {
        close();
    }
    have region->end == e by {
        close();
    }
    have region->arena->data == old(region->arena->data);
    let after = fold(arena_live_count(region->arena), { live: n - 1 });
    close();
}
```

```expect
pass
```
