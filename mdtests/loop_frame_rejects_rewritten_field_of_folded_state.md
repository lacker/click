# A loop that rewrites a folded state's base field cannot keep the frame

The negative for `loop_frame_through_folded_state_field_cells.md`, and the
state-resource twin of `loop_frame_rejects_rewritten_base_field.md`. The map
field `arena->occupied` is owned by an unfolded `state` resource, so the loop
may write it, and the body stores `arena->spare` there. Naming a pointer cell
by the load it holds applies only while the cell holds that load; after the
store, `arena->occupied[k]` reads the spare map, the clause
`arena->occupied == old(arena->occupied)` is false, and the back edge must
refuse the bundle.

```c filename=loop_frame_state_field_rewritten.c
struct arena {
    int32* occupied;
    int32* spare;
    int32 capacity;
};

void mark_and_swap(struct arena* arena, int32 start, int32 end) {
    int32 i;
    i = start;
    while (i < end) {
        arena->occupied = arena->spare;
        i = i + 1;
    }
}
```

```click
resource state(arena: struct arena*) {
    field capacity: int32;
    owns &arena->occupied;
    owns &arena->spare;
    owns arena->capacity;
    owns arena->occupied[0..arena->capacity];
    owns arena->spare[0..arena->capacity];
    fact arena->capacity == capacity;
    fact separate(
        memory(object(arena)),
        memory(arena->occupied[0..arena->capacity])
    );
    fact separate(
        memory(object(arena)),
        memory(arena->spare[0..arena->capacity])
    );
    fact separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->spare[0..arena->capacity])
    );
}

verifying "loop_frame_state_field_rewritten.c";

void mark_and_swap(struct arena* arena, int32 start, int32 end) {
    consumes st: state(arena);
    requires 0 <= start;
    requires start <= end;
    requires end <= st.capacity;
} by {
    let { capacity: c } = unfold(st);
    have end <= arena->capacity by {
        simp() using {
            end <= c;
            arena->capacity == c;
        }
    }
    step();
    step();
    loop {
        invariant start <= i;
        invariant i <= end;
        invariant end <= arena->capacity;
        invariant arena->occupied == old(arena->occupied);
        invariant forall (k: int32) {
            0 <= k and k < start implies arena->occupied[k] == old(arena->occupied[k])
        };
        decreases end - i;
        initialize by {
            simp();
        }
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
fail: closure body did not prove every invariant obligation
```
