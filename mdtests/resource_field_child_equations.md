# A child's field and argument can be the parent's field

A plain resource field is model data, so a parent can relate it to a child
without an algebraic model to match on. `arena_prefix_state` keeps its
`prefix` and `live` as fields. It passes `prefix` as the end argument of its
`marks` child and states `free.start == prefix` to set the start of its
`free` child: a field-to-field equation, where a matched arm would name a
constructor binding. Named children of an unmatched body are exposed and
refolded exactly as a matched arm's are, with `let { ... } = unfold(...)`
and the child map of `fold`.

`live_count` opens both levels, the parent and then its `free` child, whose
range starts at the child's field and so at the parent's `prefix`. It then
refolds the child at that start and the parent over both children. The
refusal of a child whose field disagrees with the parent's is
[`resource_field_child_equation_rejects_other_start.md`](resource_field_child_equation_rejects_other_start.md).

```c filename=resource_field_child_equations.c
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

verifying "resource_field_child_equations.c";

int32 live_count(struct arena* arena) {
    owns state: arena_prefix_state(arena);
    ensures result == state.live;
    ensures state.prefix == old(state.prefix);
    ensures state.live == old(state.live);
} by {
    let { marks: m, free: f } = unfold(state);
    unfold(f);
    execute();
    let f = fold(free_suffix(arena->data, arena->capacity), { start: old(state.prefix) });
    let state = fold(arena_prefix_state(arena), {
        prefix: old(state.prefix),
        live: old(state.live)
    }, { marks: m, free: f });
    simp();
}
```

```expect
pass
```
