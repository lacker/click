# Union-containing structs copied by value

A struct containing a supported union can be passed by value and copied into a
fresh address-backed aggregate. This end-to-end contract checks preservation of
ordinary and scalar/pointer union-member fields across that copy. The union itself
still has no standalone runtime value, and union member writes remain outside
this read-only slice.

```c filename=struct_union_by_value_copy.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct packet copy_packet(struct packet value) {
    return value;
}

struct packet copy_packet_pointer(struct packet value) {
    return value;
}
```

```click
verifying "struct_union_by_value_copy.c";

struct packet copy_packet(struct packet value) {
    ensures result.tag == value.tag;
    ensures result.payload.number == value.payload.number;
} by {
    auto;
}

struct packet copy_packet_pointer(struct packet value) {
    ensures result.payload.pointer == value.payload.pointer;
} by {
    auto;
}
```

```expect
pass
```
