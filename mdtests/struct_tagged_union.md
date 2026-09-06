# Read-only tagged unions

Named union members use a maximum-size, maximum-alignment LP64 layout. Each
member remains a typed read at the same byte offset, while the first slice
keeps the union address-backed: whole-union values and member writes are
rejected. A struct containing a supported union may still be copied by value;
that copy preserves the overlapping typed member views. The tag check stays
visible in the C control flow and in the Click precondition.

```c filename=struct_tagged_union.c
enum packet_kind {
    PACKET_NUMBER = 1,
    PACKET_POINTER = 2,
};

union packet_payload {
    int32 number;
    int32* pointer;
};

struct packet {
    enum packet_kind tag;
    union packet_payload payload;
};

int32 read_number(struct packet* packet) {
    if (packet->tag != PACKET_NUMBER) {
        return 0;
    }
    return packet->payload.number;
}
```

```click
verifying "struct_tagged_union.c";

int32 read_number(struct packet* packet) {
    requires loadable(packet->tag);
    requires packet->tag == 1;
    requires loadable(packet->payload.number);
    consumes packet->tag;
    consumes packet->payload.number;

    ensures result == packet->payload.number;
    produces packet->tag;
    produces packet->payload.number;
} by {
    auto;
}
```

```expect
pass
```
