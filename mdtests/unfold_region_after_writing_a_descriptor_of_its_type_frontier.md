# Unfolding a region after writing another descriptor of its type (frontier)

The same C and resources as `unfold_region_then_write_a_descriptor_of_its_type.md`,
with the proof executing the writes to `other` before it unfolds the region.
`other->pool` is then a real store, not a materialization, and the region's
descriptor is owned only inside the folded instance: no resource composition
names `object(s)`, so nothing separates the store into `other->pool` from the
body's reload of `s->pool`, which gets a name unrelated to the pool the state
was unfolded at. The unfold is refused.

```c filename=unfold_region_after_writing_a_descriptor_of_its_type_frontier.c
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

verifying "unfold_region_after_writing_a_descriptor_of_its_type_frontier.c";

int32 peek(struct slot* s, struct slot* other) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));
    owns object(other);
} by {
    step();
    step();
    step();
    let { live: n } = unfold(st);
    let { at: a, end: e } = unfold(r);
    execute();
    let r = fold(pool_slot(s), { at: a, end: e });
    let st = fold(pool_state(s->pool), { live: n });
    simp();
}
```

```expect
fail: could not evaluate instance memory body
```
