# Unfolding a region beside a viewed descriptor of its type

The companion of `unfold_region_beside_an_object_of_its_type.md` in which the
caller only views fields of the second `struct slot`. A contract `views`
clause records a loan dependency beside the frame; removing the folded
instance on `unfold` must leave that dependency state, and the state's mirror
of it, untouched, so the rewrite's own consistency check accepts the result.

```c filename=unfold_region_beside_a_viewed_descriptor_of_its_type.c
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

verifying "unfold_region_beside_a_viewed_descriptor_of_its_type.c";

int32 peek(struct slot* s, struct slot* other) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));
    views &other->pool;
    views other->at;
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
pass
```
