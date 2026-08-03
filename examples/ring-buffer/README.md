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
transition. Both `linear_ring(owner)` and `wrapped_ring(owner)` contain the
same `owned_ring_storage(owner->data)` resource. Their facts distinguish the
logical states: the linear tail is at the backing boundary, while the wrapped
tail is at index one. Because storage never leaves the enclosing ring, the
natural owner-only API is enough to preserve its identity across opaque calls.

The initializer constructs a linear ring whose occupied region ends exactly at
the backing boundary. Pushing one element writes index zero and transforms the
resource into the wrapped shape. Popping that element transforms it back to the
linear shape. A viewed accessor separately demonstrates reading through both
composite layers, and a pipeline starting from an initialized `linear_ring`
composes the full linear-to-wrapped-to-linear cycle through opaque contracts.

The example deliberately does not partition ownership into “occupied” and
“free” ranges. Those are logical roles, not ownership changes: the ring owns
its complete allocation in either state. Keeping the nested storage resource
stable is what makes the state transitions compose cleanly.

The caller supplies the metadata object and four-element backing array.
Allocation, variable capacities, general enqueue/dequeue positions, and an API
that accepts either resource state are outside this focused example's scope.
