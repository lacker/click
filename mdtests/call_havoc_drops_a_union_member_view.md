# A call that writes through a union member drops the caller's view of it

A struct with a union member materializes typed union views, and a view is
the authoritative answer to an exact typed load of that member. A call whose
write set covers the member may overwrite it, so the call havoc must drop the
view exactly as it drops a cached cell. It used to drop only cells: the view
of `g.payload.number` survived `set_number`, the load after the call read the
pre-call member, and the false `ensures result == 0` below verified (and
passed `click audit`), although `caller` returns `7 - 3`.

```c filename=call_havoc_union_view.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct packet g;

void set_number(int32* p) {
    *p = 7;
}

int32 caller() {
    int32 before;
    before = g.payload.number;
    set_number(&g.payload.number);
    return g.payload.number - before;
}
```

```click
verifying "call_havoc_union_view.c";

void set_number(int32* p) {
    owns p[0..1];
    ensures p[0] == 7;
} by auto;

int32 caller() {
    owns g.payload.number;
    requires g.payload.number == 3;
    ensures result == 0;
} by auto;
```

```expect
fail: `ensures result == 0` failed
```
