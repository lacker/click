# A loop that writes a global union member forgets the member's view

The global counterpart of
`a_loop_that_writes_a_union_member_forgets_its_view.md`. The loop writes
`g.payload.number` through `p` on every iteration. The loop head used to keep
the member's typed union view, so the load after the loop read the entry
value and the false `ensures result == 3` verified, although
`loop_writes_global` returns 9.

```c filename=a_loop_that_writes_a_global_union_member_forgets_its_view.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct packet g;

int32 loop_writes_global() {
    int32* p;
    int32 i;
    p = &g.payload.number;
    i = 0;
    while (i < 2) {
        p[0] = 9;
        i = i + 1;
    }
    return g.payload.number;
}
```

```click
verifying "a_loop_that_writes_a_global_union_member_forgets_its_view.c";

int32 loop_writes_global() {
    owns g.tag;
    owns g.payload.number;
    requires g.payload.number == 3;
    ensures result == 3;
} by {
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
fail: left side evaluated to at(<state A>, *(int32 *)((char *)&g + 8)), right side evaluated to 3
```
