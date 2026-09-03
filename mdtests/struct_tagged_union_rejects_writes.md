# Tagged-union writes stay unsupported

The read-only tagged-union slice must not turn an assignment to a union
member into an ordinary overlapping scalar store.

```c filename=struct_tagged_union_write.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

int32 write_number(struct packet* packet) {
    packet->payload.number = 7;
    return 0;
}
```

```click
verifying "struct_tagged_union_write.c";

int32 write_number(struct packet* packet) {
    ensures result == 0;
} by {
    auto;
}
```

```expect
fail: writing tagged union members
```
