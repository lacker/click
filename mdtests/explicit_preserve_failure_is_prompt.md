# Explicit preservation refuses an unproved frame promptly

The region owns the write, but its start has no lower bound placing it in the
arena's separated data range. An explicit `preserve` step names the occupancy
cell and the store's footprint. It refuses when their separation is missing.
The fixture harness checks that refusal under a pinned work limit.

```c filename=explicit_preserve_failure_is_prompt.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
};

struct region {
    struct arena* arena;
    int32 start;
    int32 end;
};

void arena_write(struct region* region, int32 value, int32 k) {
    struct arena* arena;

    arena = region->arena;
    arena->data[region->start] = value;
}
```

```click
resource arena_state(arena: struct arena*) {
    field capacity: int32;
    owns arena->data;
    owns arena->occupied;
    owns arena->capacity;
    owns arena->occupied[0..arena->capacity];
    fact arena->capacity <= 536870911;
    fact arena->capacity == capacity;
    fact separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
}

resource arena_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns *region;
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact start < end;
}

verifying "explicit_preserve_failure_is_prompt.c";

void arena_write(struct region* region, int32 value, int32 k) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    requires r.end <= st.capacity;
    requires 0 <= k and k < st.capacity;
} by {
    let { capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have to_integer(s + 1) <= to_integer(e);
    have to_integer(region->start + 1) <= to_integer(e) by {
        rewrite(region->start, s); close();
    }
    step_until(statement(2).entry);
    step();
    have region->arena->occupied[k] == at(statement(2).entry, region->arena->occupied[k]) by {
        preserve(memory(region->arena->occupied[k]), statement(2));
    }
}
```

```expect
fail: preserve separation is not exactly available
```
