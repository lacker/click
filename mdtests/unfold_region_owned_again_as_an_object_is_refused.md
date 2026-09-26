# Unfolding a region whose descriptor is also owned flat is refused

The negative of `unfold_region_beside_an_object_of_its_type.md`: the "other"
descriptor is the region's own. The contract owns `object(s)` both inside
`pool_slot(s)` and beside it, so unfolding the region would own the
descriptor twice, and the unfold is refused.

```c filename=unfold_region_owned_again_as_an_object_is_refused.c
struct pool {
    int32* data;
    int32 n;
};

struct slot {
    struct pool* pool;
    int32 at;
    int32 end;
};

int32 peek(struct slot* s) {
    struct pool* pool;

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

verifying "unfold_region_owned_again_as_an_object_is_refused.c";

int32 peek(struct slot* s) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));
    owns object(s);
} by {
    let { live: n } = unfold(st);
    let { at: a, end: e } = unfold(r);
    execute();
    let r = fold(pool_slot(s), { at: a, end: e });
    let st = fold(pool_state(s->pool), { live: n });
    simp();
}
```

```expect
fail: instance body overlaps existing ownership
```
