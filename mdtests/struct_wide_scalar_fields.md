# Wide scalar fields in structs

Struct fields may use the scalar widths already supported by C0: `uint32`,
`int64`, and `uint64`. Pointer access preserves each field's type and LP64
offset, while by-value copies preserve the same leaf types and layout.

```c filename=struct_wide_scalar_pointer.c
struct wide_packet {
    uint8 tag;
    uint32 count;
    int64 total;
    uint64 mask;
    uint8 tail;
};

uint64 update_wide_packet(struct wide_packet* packet) {
    packet->count = 7u;
    packet->total = -9;
    packet->mask = 0x123456789abcdef0ULL;
    return packet->mask;
}
```

```c filename=struct_wide_scalar_value.c
struct wide_value {
    uint32 count;
    int64 total;
    uint64 mask;
};

struct wide_value replace_wide_value(struct wide_value value) {
    value.count = 7u;
    value.total = -9;
    value.mask = 11ULL;
    return value;
}
```

```click
verifying "struct_wide_scalar_pointer.c";
verifying "struct_wide_scalar_value.c";

uint64 update_wide_packet(struct wide_packet* packet) {
    requires loadable(packet->count);
    consumes packet->count;
    requires loadable(packet->total);
    consumes packet->total;
    requires loadable(packet->mask);
    consumes packet->mask;

    ensures result == 1311768467463790320u64;
    produces packet->count;
    produces packet->total;
    produces packet->mask;
} by {
    step();
    step();
    step();
    step();
    simp();
}

struct wide_value replace_wide_value(struct wide_value value) {
    ensures result.count == 7u32;
    ensures result.total == -9;
    ensures result.mask == 11u64;
} by {
    auto;
}
```

```expect
pass
```
