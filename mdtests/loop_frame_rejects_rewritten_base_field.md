# A loop that rewrites the base field cannot keep the frame

The negative of framing a map read through a struct field. Such a frame
closes when the loop never writes the field `arena->occupied` through which
it reads the map: its value at the back edge is the pointer loaded at entry. Here the body stores `arena->spare` into that field, so at
the back edge `arena->occupied[k]` reads the spare map. The loop keeps the
field readable at its head with `arena->occupied == old(arena->occupied)`,
and that clause, the frame over it, is false after the store: the two maps
are separate and nonempty whenever the body runs. The maintenance proof
checks the pointer invariant explicitly at the back edge.

```c filename=loop_frame_field_rewritten.c
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
verifying "loop_frame_field_rewritten.c";

void mark_and_swap(struct arena* arena, int32 start, int32 end) {
    owns *arena;
    owns arena->occupied[0..arena->capacity];
    owns arena->spare[0..arena->capacity];
    requires separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
    requires separate(
        memory(*arena),
        memory(arena->spare[0..arena->capacity])
    );
    requires separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->spare[0..arena->capacity])
    );
    requires 0 <= start;
    requires start <= end;
    requires end <= arena->capacity;
} by {
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
            close();
        }
        maintain by {
            step();
            step();
            have arena->occupied == old(arena->occupied) by { close(); }
        }
    }
}
```

```expect
fail: `have` failed for `arena->occupied == old(arena->occupied)`
```
