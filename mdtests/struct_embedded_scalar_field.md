# Embedded struct scalar fields

An embedded struct is an aggregate place: selecting its scalar member combines
the outer and inner ABI offsets without loading the aggregate as a runtime
value. Leaf field resources use the same nested address.

```c filename=struct_embedded_scalar_field.c
struct inner {
    int32 value;
    uint8 flag;
};

struct outer {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

int32 write_nested(struct outer* packet) {
    packet->inner.value = 7;
    return packet->inner.value;
}
```

```click
verifying "struct_embedded_scalar_field.c";

int32 write_nested(struct outer* packet) {
    requires loadable(packet->inner.value);
    consumes packet->inner.value;

    ensures result == packet->inner.value;
    produces packet->inner.value;
} by {
    step();
    step();
    simp();
}
```

```expect
pass
```
