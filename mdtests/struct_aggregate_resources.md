# Aggregate struct resource places expand to typed leaf ranges

An embedded struct place can be named directly by each resource verb. Click
expands the place into its leaf field ranges, retaining each leaf's ABI width
instead of pretending that a mixed-width aggregate is one int32 range.

```c filename=struct_aggregate_resources.c
struct inner {
    int32 count;
    uint8 flag;
    struct inner* next;
};

struct outer {
    uint8 tag;
    struct inner inner;
    int32 tail;
};

struct array_outer {
    struct inner items[2];
};

int32 read_inner(struct outer* packet) {
    return packet->inner.count;
}

int32 write_inner(struct outer* packet) {
    packet->inner.count = 7;
    packet->inner.flag = 1;
    return packet->inner.count;
}

int32 own_inner(struct outer* packet) {
    packet->inner.count = 11;
    packet->inner.flag = 1;
    return packet->inner.count;
}

int32 write_array(struct array_outer* packet) {
    packet->items[1].count = 13;
    packet->items[1].flag = 1;
    return packet->items[1].count;
}
```

```click
verifying "struct_aggregate_resources.c";

int32 read_inner(struct outer* packet) {
    views packet->inner;
    ensures result == packet->inner.count by auto;
}

int32 write_inner(struct outer* packet) {
    consumes packet->inner;
    ensures result == 7 by auto;
    produces packet->inner by auto;
}

int32 own_inner(struct outer* packet) {
    owns packet->inner by auto;
    ensures result == 11 by auto;
}

int32 write_array(struct array_outer* packet) {
    consumes packet->items;
    ensures result == 13 by auto;
    produces packet->items by auto;
}
```

```expect
pass
```
