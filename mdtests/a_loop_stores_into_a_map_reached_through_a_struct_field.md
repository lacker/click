# A loop stores into a map reached through a struct field

A loop whose frame owns `p->f[0..n]` stores to `p->f[i]` under
`0 <= i < n`. The store's pointer is read from the field at that program
point; the frame's map must cover it there. This is the gate's reduction of
the nightly fixtures
`loop_entry_keeps_unfolded_state_fields_beside_its_owned_map.md` and
`loop_frame_keeps_a_two_hop_map_beside_a_written_array.md`; the second also
reaches the map through another struct.

```c filename=a_loop_stores_into_a_map_reached_through_a_struct_field.c
struct arena {
    int32* data;
    int32 capacity;
};

void mark_all(struct arena* arena) {
    int32 i;
    i = 0;
    while (i < arena->capacity) {
        arena->data[i] = 1;
        i = i + 1;
    }
}
```

```click
verifying "a_loop_stores_into_a_map_reached_through_a_struct_field.c";

void mark_all(struct arena* arena) {
    views arena->data;
    views arena->capacity;
    owns arena->data[0..arena->capacity];
    requires 0 <= arena->capacity;
} by {
    step();
    step();
    loop {
        decreases (arena->capacity - i);
        owns arena->data[0..arena->capacity];
        invariant 0 <= i and i <= arena->capacity;
        initialize by solve();
        preserve by {
            have separate(memory(*arena), memory(arena->data[0..arena->capacity])) by solve();
            mark write;
            step();
            transport(at(write, arena->capacity) == at(write, arena->capacity),
                arena->capacity == at(write, arena->capacity)) using {
                at(write, separate(memory(*arena), memory(arena->data[0..arena->capacity])));
                0 <= i;
                i < at(write, arena->capacity);
            };
            step();
            solve();
        }
    }
    step();
}
```

```expect
pass
```
