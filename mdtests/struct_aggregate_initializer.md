# Positional initializers for copyable structs

Copyable struct declarations accept positional aggregate initializers. Nested
structs and fixed-dimensional scalar-array fields keep their declared shape;
omitted members and cells are initialized to zero, and the initialized object
is still the ordinary fresh address-backed struct value.

```c filename=struct_aggregate_initializer.c
struct inner {
    int32 value;
    uint8 enabled;
};

struct packet {
    uint8 tag;
    struct inner inner;
    int32 tail;
    uint8 bytes[2][3];
    int32* pointer;
};

int32 struct_aggregate_initializer() {
    struct packet packet = {9, {11, 1}, 13, {{2, 3}, {4}}};
    return packet.tag + packet.inner.value + packet.inner.enabled
        + packet.tail + packet.bytes[0][1] + packet.bytes[1][2]
        + (packet.pointer == 0);
}
```

```c filename=struct_aggregate_initializer_embedded_array.c
struct array_leaf {
    int32 value;
    uint8 enabled;
};

struct array_packet {
    struct array_leaf items[2][2];
    int32 tail;
};

int32 struct_aggregate_initializer_embedded_array() {
    struct array_packet packet = {{{{1, 2}, {3}}, {{4}, {5, 6}}}};
    return packet.items[0][0].value + packet.items[0][0].enabled
        + packet.items[0][1].value + packet.items[1][0].value
        + packet.items[1][1].value + packet.items[1][1].enabled
        + (packet.tail == 0);
}
```

```click
verifying "struct_aggregate_initializer.c";
verifying "struct_aggregate_initializer_embedded_array.c";

int32 struct_aggregate_initializer() {
    ensures result == 38;
} by {
    auto;
}

int32 struct_aggregate_initializer_embedded_array() {
    ensures result == 22;
} by {
    auto;
}
```

```expect
pass
```
