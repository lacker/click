# A loop that writes a union member forgets the member's view

A by-value copy of a struct with a union member records typed union views,
and a view is the authoritative answer to an exact typed load of that
member. The loop below writes the member through `p` on every iteration, so
the loop head has to forget the view exactly as it forgets a cell. It used to
forget cells only: the view of `source.payload.number` survived the loop, the
load after it read the pre-loop member, and the false `ensures result == 3`
verified, although `loop_writes_union` returns 9. The straight-line store
was always refused; only the loop head missed the view.

```c filename=a_loop_that_writes_a_union_member_forgets_its_view.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct packet g;

int32 loop_writes_union() {
    struct packet source;
    int32* p;
    int32 i;
    source = g;
    p = &source.payload.number;
    i = 0;
    while (i < 2) {
        p[0] = 9;
        i = i + 1;
    }
    return source.payload.number;
}
```

```click
verifying "a_loop_that_writes_a_union_member_forgets_its_view.c";

int32 loop_writes_union() {
    owns g.tag;
    owns g.payload.number;
    requires g.payload.number == 3;
    ensures result == 3;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    execute();
    simp();
}
```

```expect
fail: left side evaluated to at(<state A>, *(int32 *)((char *)&source + 8)), right side evaluated to 3
```
