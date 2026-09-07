# an aggregate copy leaves no stale value in a field it cannot carry

Struct assignment copies every member (C11 6.5.16.1p2). The kernel's aggregate
copy handles a fixed list of leaf types, and a union-containing layout routes
whole-struct assignment through it. A field type outside that list must not
leave the destination's previous value in place: the old contents are readable
afterwards even though no execution of the copy produces them.

Here `dst.fp` holds a local array address before the copy and the source's is
null, so reading it back as the old address is wrong. The copy now drops those
cells instead, and the read is reported rather than answered.

```c filename=aggregate_copy_skipped_field_rejected.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
    float* data;
};

int32 aggregate_copy_skipped_field_rejected(struct packet* source) {
    float storage[1];
    struct packet destination;
    destination.tag = 1;
    destination.data = storage;
    destination = *source;
    return destination.tag * 10 + (destination.data == 0);
}
```

```click
verifying "aggregate_copy_skipped_field_rejected.c";

int32 aggregate_copy_skipped_field_rejected(struct packet* source) {
    requires loadable(source->tag);
    requires loadable(source->payload.number);
    requires loadable(source->data);
    requires source->tag == 2;
    requires source->data == 0;
    consumes source->tag;
    consumes source->payload.number;
    consumes source->data;
    ensures result == 20;
    produces source->tag;
    produces source->payload.number;
    produces source->data;
}
```

```expect
fail: read of uninitialized storage
```
