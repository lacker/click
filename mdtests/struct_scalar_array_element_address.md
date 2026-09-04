# Addresses of scalar array cells in structs

Taking the address of a scalar cell inside an inline struct array preserves
the struct field offset, row-major index, element width, and allocation
provenance. A pointer store through that address updates the same cell selected
by the original expression.

```c filename=struct_scalar_array_element_address.c
struct packet {
    uint8 tag;
    int32 values[2][3];
};

int32 update_value(struct packet* packet) {
    int32* value_pointer;
    value_pointer = &packet->values[1][2];
    *value_pointer = 7;
    return packet->values[1][2];
}
```

```c filename=struct_scalar_array_byte_address.c
struct byte_packet {
    uint8 tag;
    uint8 bytes[3][2];
};

uint8 update_byte(struct byte_packet* packet) {
    uint8* byte_pointer;
    byte_pointer = &packet->bytes[2][1];
    *byte_pointer = 9;
    return packet->bytes[2][1];
}
```

```click
verifying "struct_scalar_array_element_address.c";
verifying "struct_scalar_array_byte_address.c";

int32 update_value(struct packet* packet) {
    requires loadable(packet->values[1][2]);
    consumes packet->values[1][2];

    ensures result == 7;
    produces packet->values[1][2];
} by {
    step();
    step();
    step();
    step();
    simp();
}

uint8 update_byte(struct byte_packet* packet) {
    requires loadable(packet->bytes[2][1]);
    consumes packet->bytes[2][1];

    ensures result == 9;
    produces packet->bytes[2][1];
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
