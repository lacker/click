# Resource fields cannot select a memory-range endpoint

An allocator partition needs to retain the endpoint of a prior allocation and
use it as the start of the remaining free range. A resource field can remember
that value for pure facts, but it is not a current C expression and therefore
cannot select the owned range. This is the exact boundary preventing the
pipeline-specific second-allocation state from becoming a symbolic partition.

```c filename=resource_field_memory_endpoint_rejected.c
struct buffer {
    int32* data;
    int32 capacity;
};
```

```click
spec enum SuffixTag { Available }

resource suffix_after_prefix(buffer: struct buffer*) {
    field tag: SuffixTag;
    field start: int32;
    match tag {
        SuffixTag::Available => {
            owns buffer->data;
            owns buffer->capacity;
            owns buffer->data[start..buffer->capacity];
        },
    }
}
```

```expect
fail: memory segment start must be a current C expression
```
