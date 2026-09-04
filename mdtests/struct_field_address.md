# Address nested struct fields

Taking the address of a scalar leaf field preserves the containing allocation
and the complete ABI offset through each embedded struct. A store through the
result therefore updates the same leaf selected by the source expression.

```c filename=struct_field_address.c
struct inner {
    uint8 flag;
    int32 value;
};

struct outer {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

int32 update_nested(struct outer* packet) {
    int32* value_pointer;
    value_pointer = &packet->inner.value;
    *value_pointer = 7;
    return packet->inner.value;
}

int32 update_direct(struct outer* packet) {
    int32* tail_pointer;
    tail_pointer = &packet->tail;
    *tail_pointer = 9;
    return packet->tail;
}
```

```click
verifying "struct_field_address.c";

int32 update_nested(struct outer* packet) {
    requires loadable(packet->inner.value);
    consumes packet->inner.value;

    ensures result == 7;
    produces packet->inner.value;
} by {
    step();
    step();
    step();
    step();
    simp();
}

int32 update_direct(struct outer* packet) {
    requires loadable(packet->tail);
    consumes packet->tail;

    ensures result == 9;
    produces packet->tail;
} by {
    step();
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
