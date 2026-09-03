# free still rejects an unowned allocation

Searching all allocation authorities must not turn an unrelated external
pointer into a heap allocation.

```c filename=heap_free_missing_allocation_authority.c
struct two_buffers {
    int32* first;
    int32* second;
};

void free_second_without_authority(struct two_buffers* buffers) {
    free(buffers->second);
}
```

```click
resource first_buffer_owned(buffers: struct two_buffers*) {
    owns buffers->first;
    owns buffers->second;
    contains allocation(buffers->first, 4);
    owns buffers->first[0..1];
}

verifying "heap_free_missing_allocation_authority.c";

void free_second_without_authority(struct two_buffers* buffers) {
    consumes first_buffer_owned(buffers);
    mutable buffers->second;
} by {
    unfold(first_buffer_owned(buffers));
    execute();
    simp();
}
```

```expect
fail: cannot free a pointer that is not a live heap allocation
```
