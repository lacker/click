# Multidimensional arrays of embedded structs preserve row-major stride

Fixed dimensions on an inline array of embedded structs are retained in C0
metadata. Indexing them uses the C row-major offset, with each element stepping
by the nested struct's complete ABI size.

```c filename=struct_multidimensional_embedded_array.c
struct point {
    int32 value;
    uint8 flag;
};

struct packet {
    uint8 tag;
    struct point points[2][2];
    int32 tail;
};

int32 read_point(struct packet* packet) {
    packet->points[1][1].value = 7;
    return packet->points[1][1].value;
}
```

```click
verifying "struct_multidimensional_embedded_array.c";

int32 read_point(struct packet* packet) {
    requires loadable(packet->points[1][1].value);
    consumes packet->points[1][1].value;
    ensures result == 7;
    produces packet->points[1][1].value;
} by {
    step();
    step();
    simp();
}
```

```expect
pass
```
