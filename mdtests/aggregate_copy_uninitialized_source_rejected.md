# an aggregate copy from an uninitialized source is rejected

Whole-struct assignment copies every member (C11 6.5.16.1p2). A
union-containing layout routes whole-struct assignment through the kernel's
aggregate copy, which copies a source cell only when one is present. With no
source cell the destination's own cell survived untouched, so the copy left
the old value readable even though the assignment was supposed to overwrite
it.

Here `source` is never written, so `destination.tag` is indeterminate after
`destination = source` and the `7` written before the copy must not survive.
The copy now reports the read of uninitialized storage, matching what the
same assignment between plain structs already does.

```c filename=aggregate_copy_uninitialized_source_rejected.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

int32 aggregate_copy_uninitialized_source_rejected() {
    struct packet source;
    struct packet destination;
    destination.tag = 7;
    destination = source;
    return destination.tag;
}
```

```click
verifying "aggregate_copy_uninitialized_source_rejected.c";

int32 aggregate_copy_uninitialized_source_rejected() {
    ensures result == 7;
}
```

```expect
fail: read of uninitialized storage
```
