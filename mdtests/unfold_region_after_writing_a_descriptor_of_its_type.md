# Unfolding a region after writing another descriptor of its type

The same C and resources as `unfold_region_then_write_a_descriptor_of_its_type.md`,
with the proof executing the writes to `other` before it unfolds the region.
`other->pool` is then a real store, and the region's descriptor `object(s)`
is owned only inside the folded instance `r`. The unmatched body's cells are
named at entry, and the store keeps them: the partition law places a cell a
held instance owns one body layer down apart from a write into a different
owned member (`object(other)`), exactly as it does for two flat members. The
body's reload of `s->pool` at the unfold is therefore the pool the state was
unfolded at, and the region unfolds and folds back.

```c filename=unfold_region_after_writing_a_descriptor_of_its_type.c
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

verifying "unfold_region_after_writing_a_descriptor_of_its_type.c";

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
pass
```
