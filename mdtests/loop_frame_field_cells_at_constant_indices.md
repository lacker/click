# Framing constant cells of a map reached through a struct field

A loop marks `arena->occupied[i]` for `i` in `[start, end)` and carries, one
invariant per cell, that the cells `arena->occupied[0]` and
`arena->occupied[1]` below `start` keep their entry values. Each cell's
back-edge member has a viewability obligation at the back edge and at
function entry, and the smart closer discharges both by transport from the
entry viewability of the map. That needs a source spelling of each cell
through the field, `arena->occupied[1]` for the element at a constant byte
displacement from the field's pointer, not only the element at the pointer
itself.

The second cell's member is also guarded by the first cell's invariant,
which the back edge states as the bare clause: a later member is guarded by
an earlier clause, not by the whole earlier member, so the bundle grows with
the declarations instead of doubling with each one.

```c filename=mark_tail.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
};

void mark_tail(struct arena* arena, int32 start, int32 end) {
    int32 i;
    i = start;
    while (i < end) {
        arena->occupied[i] = 1;
        i = i + 1;
    }
}
```

```click
verifying "mark_tail.c";

void mark_tail(struct arena* arena, int32 start, int32 end) {
    owns object(arena);
    owns arena->occupied[0..arena->capacity];
    requires separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
    requires 2 <= start;
    requires start <= end;
    requires end <= arena->capacity;
} by {
    step();
    step();
    loop {
        owns arena->occupied[0..arena->capacity];
        invariant start <= i;
        invariant i <= end;
        invariant end <= arena->capacity;
        invariant arena->occupied[0] == old(arena->occupied[0]);
        invariant arena->occupied[1] == old(arena->occupied[1]);
        decreases end - i;
        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
