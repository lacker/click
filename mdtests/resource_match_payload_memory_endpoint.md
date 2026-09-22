# A matched resource payload can select a memory-range endpoint

A constructor payload is stable model data while its resource is folded. After
matching the model, the payload can select a symbolic suffix and bound a
quantified fact over that suffix. Unfolding and folding preserve both without
enumerating the range.

```c filename=resource_match_payload_memory_endpoint.c
struct buffer {
    int32* data;
    int32 capacity;
};

void keep(struct buffer* buffer) {}
```

```click
spec enum SuffixTag { Available(int32) }

resource suffix_after_prefix(buffer: struct buffer*) {
    field tag: SuffixTag;
    match tag {
        SuffixTag::Available(start) => {
            owns &buffer->data;
            owns buffer->capacity;
            owns buffer->data[start..buffer->capacity];
            fact 0 <= start;
            fact start <= buffer->capacity;
            fact forall (k: int32) {
                0 <= k and start <= k and k < buffer->capacity implies
                    buffer->data[k] == 0
            };
        },
    }
}

verifying "resource_match_payload_memory_endpoint.c";

void keep(struct buffer* buffer) {
    owns suffix: suffix_after_prefix(buffer);
} by {
    match suffix.tag {
        SuffixTag::Available(start) => {
            unfold(suffix);
            execute();
            let suffix = fold(suffix_after_prefix(buffer), {
                tag: SuffixTag::Available(start)
            });
            simp();
        },
    }
}
```

```expect
pass
```
