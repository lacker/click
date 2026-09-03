# free selects the matching authority among multiple allocations

Heap-free lookup must not stop at the first allocation token in the resource
context. The second independently owned allocation is still a valid heap
base.

```c filename=heap_free_matching_allocation_authority.c
struct two_buffers {
    int32* first;
    int32* second;
};

void free_second_then_first(struct two_buffers* buffers) {
    free(buffers->second);
    free(buffers->first);
}
```

```click
resource two_buffers_owned(buffers: struct two_buffers*) {
    owns buffers->first;
    owns buffers->second;
    contains allocation(buffers->first, 4);
    contains allocation(buffers->second, 4);
    owns buffers->first[0..1];
    owns buffers->second[0..1];
    fact separate(
        memory(object(buffers)),
        memory(buffers->first[0..1])
    );
    fact separate(
        memory(object(buffers)),
        memory(buffers->second[0..1])
    );
}

verifying "heap_free_matching_allocation_authority.c";

void free_second_then_first(struct two_buffers* buffers) {
    consumes two_buffers_owned(buffers);
    mutable buffers->first, buffers->second;
} by {
    unfold(two_buffers_owned(buffers));
    execute();
    frame();
    simp();
}
```

```expect
pass
```
