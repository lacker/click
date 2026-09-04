# Designated initializers for copyable structs

Copyable struct-valued locals accept C field designators, including
declaration-order-independent designators and designators that name a nested
embedded field. A designated initializer starts from a complete zero value, so
omitted fields remain zero. A nested aggregate can also contain its own field
designators.

```c filename=struct_designated_initializer.c
struct inner {
    int32 value;
    uint8 enabled;
};

struct packet {
    uint8 tag;
    struct inner inner;
    int32 tail;
    uint8 bytes[2];
    int32* pointer;
};

int32 direct_designators() {
    struct packet packet = {
        .tail = 13,
        .inner.value = 11,
        .tag = 9,
        .inner.enabled = 1,
    };
    return packet.tag + packet.inner.value + packet.inner.enabled
        + packet.tail + packet.bytes[0] + packet.bytes[1]
        + (packet.pointer == 0);
}

int32 nested_designator() {
    struct packet packet = {
        .inner = { .enabled = 4 },
        .tail = 3,
    };
    return packet.tag + packet.inner.value + packet.inner.enabled
        + packet.tail + (packet.pointer == 0);
}
```

```click
verifying "struct_designated_initializer.c";

int32 direct_designators() {
    ensures result == 35;
} by {
    auto;
}

int32 nested_designator() {
    ensures result == 8;
} by {
    auto;
}
```

```expect
pass
```
