# Multidimensional embedded struct arrays remain outside the slice

The first slice supports one-dimensional inline arrays of embedded structs.
Nested array dimensions are rejected explicitly until their row-stride model
is added.

```c filename=struct_multidimensional_embedded_array_rejected.c
struct point {
    int32 value;
};

struct packet {
    struct point points[2][2];
};

int32 read_point(struct packet* packet) {
    return packet->points[1][1].value;
}
```

```click
verifying "struct_multidimensional_embedded_array_rejected.c";

int32 read_point(struct packet* packet) {
    ensures result == 0 by auto;
}
```

```expect
fail: multidimensional arrays of embedded structs are not supported
```
