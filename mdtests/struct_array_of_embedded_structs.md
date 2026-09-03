# One-dimensional arrays of embedded structs preserve element stride

An inline array of embedded structs keeps each element's complete ABI size,
including padding. Indexing the field selects an aggregate address, so the
terminal scalar member is accessed at the nested element offset.

```c filename=struct_array_of_embedded_structs.c
struct point {
    int32 value;
    uint8 flag;
};

struct packet {
    uint8 tag;
    struct point points[2];
    int32 tail;
};

int32 write_point(struct packet* packet) {
    packet->points[1].value = 7;
    return packet->points[1].value;
}
```

```click
verifying "struct_array_of_embedded_structs.c";

int32 write_point(struct packet* packet) {
    requires loadable(packet->points[1].value);
    consumes packet->points[1].value;
    ensures result == 7;
    produces packet->points[1].value;
} by {
    step();
    step();
    simp();
}
```

```expect
pass
```
