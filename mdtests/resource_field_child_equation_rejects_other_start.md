# A child whose field disagrees with the parent's field is refused

`arena_prefix_state` sets its `free` child's start to its own `prefix` field
with the equation `free.start == prefix`. Folding the parent checks that
equation against the child it is handed. Here the child was refolded to start
at the capacity instead, which the parent's `prefix` is not known to equal, so
the parent fold is refused. The positive fixture is
[`resource_field_child_equations.md`](resource_field_child_equations.md).

```c filename=resource_field_child_equation_rejects_other_start.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

int32 live_count(struct arena* arena) {
    return arena->live_regions;
}
```

```click
resource occupied_marks(occupied: int32*, end: int32) {
    field count: int32;
    owns occupied[0..end];
    fact 0 <= end;
    fact forall (k: int32) { 0 <= k and k < end implies occupied[k] == 1 };
}

resource free_suffix(data: int32*, capacity: int32) {
    field start: int32;
    owns data[start..capacity];
    fact 0 <= start;
    fact start <= capacity;
}

resource arena_prefix_state(arena: struct arena*) {
    field prefix: int32;
    field live: int32;
    owns &arena->data;
    owns &arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    owns marks: occupied_marks(arena->occupied, prefix);
    owns free: free_suffix(arena->data, arena->capacity);
    fact marks.count == live;
    fact free.start == prefix;
    fact arena->live_regions == live;
}

verifying "resource_field_child_equation_rejects_other_start.c";

int32 live_count(struct arena* arena) {
    owns state: arena_prefix_state(arena);
    ensures result == state.live;
    ensures state.prefix == old(state.prefix);
    ensures state.live == old(state.live);
} by {
    let { marks: m, free: f } = unfold(state);
    unfold(f);
    let f = fold(free_suffix(arena->data, arena->capacity), { start: arena->capacity });
    let state = fold(arena_prefix_state(arena), {
        prefix: old(state.prefix),
        live: old(state.live)
    }, { marks: m, free: f });
    execute();
    simp();
}
```

```expect
fail: selected child does not satisfy the proposed parent model
```
