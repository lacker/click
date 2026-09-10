# Ring Buffer

This project verifies a fixed-capacity ring buffer whose occupied region moves
between a contiguous linear shape and a wrapped two-segment shape.

```c
struct ring_buffer {
    int32 head;
    int32 tail;
    int32* data;
};
```

The capacity is fixed at four elements so the example can focus on the state
transition. `ring_frame(owner)` holds the head, the backing pointer, and the
four-element storage: everything the state transition leaves alone. Both
`linear_ring(owner)` and `wrapped_ring(owner)` own `owner->tail` and contain
that same frame. Their facts distinguish the logical states: the linear tail is
at the backing boundary, while the wrapped tail is at index one.

The initializer constructs a linear ring whose occupied region ends exactly at
the backing boundary. Pushing one element writes index zero and moves the tail,
so it owns exactly `owner->tail` and `owner->data[0..1]` and views the head,
the backing pointer, and `owner->data[1..4]`; the caller unfolds the ring
around the call and refolds it in the wrapped shape. Popping that element
writes only `owner->tail`, so it owns that field and views the rest. A viewed accessor separately demonstrates reading through both
composite layers, and a pipeline starting from an initialized `linear_ring`
composes the full linear-to-wrapped-to-linear cycle through opaque contracts.

The example deliberately does not partition ownership into “occupied” and
“free” ranges. Those are logical roles, not ownership changes: the ring owns
its complete allocation in either state. Keeping the frame resource stable is
what makes the state transitions compose cleanly.

The caller supplies the metadata object and four-element backing array.
Allocation, variable capacities, general enqueue/dequeue positions, and an API
that accepts either resource state are outside this focused example's scope.
