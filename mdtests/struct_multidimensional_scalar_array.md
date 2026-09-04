# Multidimensional scalar arrays in structs

Inline scalar arrays in structs retain their declared dimensions. Indexing a
field flattens the indices in C row-major order while preserving the field's
ABI offset and element width. The same flattened cells participate in
by-value struct copies.

```c filename=struct_multidimensional_scalar_array.c
struct value_packet {
    uint8 tag;
    int32 values[2][3];
};

int32 update_values(struct value_packet* packet) {
    packet->values[1][2] = 7;
    return packet->values[1][2];
}
```

```c filename=struct_multidimensional_scalar_array_bytes.c
struct byte_packet {
    uint8 tag;
    uint8 bytes[3][2];
};

uint8 update_bytes(struct byte_packet* packet) {
    packet->bytes[2][1] = 9;
    return packet->bytes[2][1];
}
```

```c filename=struct_multidimensional_scalar_array_finish.c
struct copy_packet {
    uint8 tag;
    int32 values[2][3];
};

struct copy_packet finish(struct copy_packet value) {
    value.values[1][2] = 7;
    return value;
}
```

```c filename=struct_multidimensional_scalar_array_run.c
struct copy_packet {
    uint8 tag;
    int32 values[2][3];
};

int32 run_struct_multidimensional_scalar_array() {
    struct copy_packet original;
    struct copy_packet copy;
    original.tag = 8;
    original.values[0][0] = 1;
    original.values[0][1] = 2;
    original.values[0][2] = 3;
    original.values[1][0] = 4;
    original.values[1][1] = 5;
    original.values[1][2] = 6;
    copy = finish(original);
    return original.values[1][2] * 10 + copy.values[1][2] + original.tag;
}
```

```click
verifying "struct_multidimensional_scalar_array.c";
verifying "struct_multidimensional_scalar_array_bytes.c";
verifying "struct_multidimensional_scalar_array_finish.c";
verifying "struct_multidimensional_scalar_array_run.c";

int32 update_values(struct value_packet* packet) {
    requires loadable(packet->values[1][2]);
    consumes packet->values[1][2];
    ensures result == 7;
    produces packet->values[1][2];
} by {
    step();
    step();
    simp();
}

uint8 update_bytes(struct byte_packet* packet) {
    requires loadable(packet->bytes[2][1]);
    consumes packet->bytes[2][1];
    ensures result == 9;
    produces packet->bytes[2][1];
} by {
    step();
    step();
    simp();
}

struct copy_packet finish(struct copy_packet value) {
    ensures result.values[1][2] == 7;
} by {
    auto;
}

int32 run_struct_multidimensional_scalar_array() {
    ensures result == 75;
} by {
    execute();
    simp();
}
```

```expect
pass
```
