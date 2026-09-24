# One unfold pattern names children and scalar fields together

A `let { ... } = unfold(parent)` pattern may mix the parent's child slots and
its C-typed fields. `arena_prefix_state` owns the `marks` and `free` children
and carries the `prefix` and `live` fields. Unfolding it names both children,
which stay folded and owned under their names, and both field values, which
are proof names for the rest of the function. The refold supplies the fields
by those names and the children by theirs, and the child `free` is refolded at
the bound `p`.

This is the let-bound form of
[`resource_field_child_equations.md`](resource_field_child_equations.md),
whose proof spells the same values as `old(state.prefix)` and
`old(state.live)`.

```c filename=resource_unfold_binds_children_and_fields.c
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

verifying "resource_unfold_binds_children_and_fields.c";

int32 live_count(struct arena* arena) {
    owns state: arena_prefix_state(arena);
    ensures result == state.live;
    ensures state.prefix == old(state.prefix);
    ensures state.live == old(state.live);
} by {
    let { marks: m, prefix: p, free: f, live: n } = unfold(state);
    unfold(f);
    execute();
    let f = fold(free_suffix(arena->data, arena->capacity), { start: p });
    let state = fold(arena_prefix_state(arena), {
        prefix: p,
        live: n
    }, { marks: m, free: f });
    simp();
}
```

```expect
pass
```
