# an aggregate return from an uninitialized source is rejected

Whole-struct assignment copies every member (C11 6.5.16.1p2), and the same
holds for the aggregate copies a function return performs: materializing the
return value into the caller's slot and assigning the call result to a local.
The kernel's aggregate copy skips a carried field with no source cell, so a
function returning a struct with an unwritten field used to hand the caller a
value whose missing field silently became symbolic instead of reporting an
uninitialized read.

Here `make_packet` never writes `p.payload`, so returning `p` reads
uninitialized storage. The centralized aggregate-copy check now reports that
read at return materialization, which also stops `read_payload` from ever
observing the indeterminate field.

```c filename=aggregate_return_uninitialized_source_rejected.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct packet make_packet() {
    struct packet p;
    p.tag = 1;
    return p;
}

int32 read_payload() {
    struct packet q = make_packet();
    return q.payload.number;
}
```

```click
verifying "aggregate_return_uninitialized_source_rejected.c";

struct packet make_packet() {
    ensures result.tag == 1;
}

int32 read_payload() {
    ensures result == result;
}
```

```expect
fail: read of uninitialized storage
```
