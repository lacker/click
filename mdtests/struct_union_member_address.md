# Addresses of tagged-union members

Taking the address of a supported union member preserves the containing
allocation and the member's scalar or pointer type. The pointer can then be
used for a read without materializing a whole-union value; direct union-member
writes remain outside the read-only union slice.

```c filename=struct_union_member_address.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

int32 read_number_through_address(struct packet* packet) {
    int32* number_pointer;
    number_pointer = &packet->payload.number;
    return *number_pointer;
}
```

```click
verifying "struct_union_member_address.c";

int32 read_number_through_address(struct packet* packet) {
    requires loadable(packet->payload.number);
    consumes packet->payload.number;

    ensures result == packet->payload.number;
    produces packet->payload.number;
} by {
    auto;
}
```

```expect
pass
```
