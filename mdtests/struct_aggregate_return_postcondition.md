# Pointer-backed aggregate return postconditions

A helper that returns an aggregate loaded through a pointer should expose a
fresh aggregate result whose scalar and nested fields equal the source
snapshot, without turning the source pointer into an alias of the result.

```c filename=struct_aggregate_return_postcondition.c
struct inner {
    int32 value;
    uint8 flag;
};

struct packet {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

struct packet clone_packet(struct packet* source) {
    return *source;
}
```

```click
verifying "struct_aggregate_return_postcondition.c";

struct packet clone_packet(struct packet* source) {
    views source->tag;
    views source->inner.value;
    views source->inner.flag;
    views source->tail;
    ensures result.tag == source->tag;
    ensures result.inner.value == source->inner.value;
    ensures result.inner.flag == source->inner.flag;
    ensures result.tail == source->tail;
} by {
    auto;
}
```

```expect
pass
```
