# Writing another descriptor of the region's type after unfolding it

The region is unfolded while the second `struct slot` still holds its
materialized cells, then the C writes that descriptor's `at` and `pool`
fields. The descriptor `object(s)` and `object(other)` are then two owned
members of the frame, so the writes leave `s->pool` in place and the fold
finds the range the unfold produced.

```c filename=unfold_region_then_write_a_descriptor_of_its_type.c
struct pool {
    int32* data;
    int32 n;
};

struct slot {
    struct pool* pool;
    int32 at;
    int32 end;
};

int32 peek(struct slot* s, struct slot* other) {
    struct pool* pool;

    other->at = 7;
    other->pool = 0;
    pool = s->pool;
    return pool->n;
}
```

```click
resource pool_state(pool: struct pool*) {
    field live: int32;
    owns &pool->data;
    owns pool->n;
    fact 0 <= live;
}

resource pool_slot(s: struct slot*) {
    field at: int32;
    field end: int32;
    owns object(s);
    owns s->pool->data[at..end];
    fact s->at == at;
    fact s->end == end;
    fact 0 <= at;
    fact at < end;
}

verifying "unfold_region_then_write_a_descriptor_of_its_type.c";

int32 peek(struct slot* s, struct slot* other) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));
    owns object(other);
} by {
    let { live: n } = unfold(st);
    let { at: a, end: e } = unfold(r);
    step();
    step();
    step();
    execute();
    let r = fold(pool_slot(s), { at: a, end: e });
    let st = fold(pool_state(s->pool), { live: n });
    simp();
}
```

```expect
pass
```
