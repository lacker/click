# Inline byte arrays in structs

Fixed scalar arrays in a struct retain their inline ABI shape. Indexed field
access uses byte-width pointer arithmetic while the surrounding object range
covers the complete struct, including the preceding byte field.

```c filename=struct_inline_byte_array.c
struct packet {
    uint8 tag;
    uint8 buf[16];
};

uint8 write_packet(struct packet* packet) {
    packet->buf[2] = 7;
    return packet->buf[2];
}
```

```c filename=struct_inline_byte_array_parameter.c
struct item {
    uint8 buf[8];
};

uint8 write_array_item(struct item items[2]) {
    items[1].buf[2] = 7;
    return items[1].buf[2];
}
```

```click
verifying "struct_inline_byte_array.c";
verifying "struct_inline_byte_array_parameter.c";

uint8 write_packet(struct packet* packet) {
    requires loadable(packet->buf);
    consumes packet->buf;

    ensures result == 7;
    produces packet->buf;
} by {
    step();
    step();
    simp();
}

uint8 write_array_item(struct item items[2]) {
    requires loadable(items[0..2]);
    consumes items[0..2];

    ensures result == 7;
    produces items[0..2];
} by {
    step();
    step();
    simp();
}
```

```expect
pass
```
