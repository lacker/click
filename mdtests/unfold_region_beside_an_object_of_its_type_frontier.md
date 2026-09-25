# Unfolding a region beside an owned object of its type (frontier)

`pool_slot(s)` owns the descriptor `object(s)` and `s->pool->data[at..end]`.
With the pool state unfolded, `peek` unfolds the slot to read through it, as
the arena's `arena_read` does. The unfold evaluates the slot body's range,
whose base loads `s->pool`, against the body's own memory; when the caller
also owns `object(other)`, a second `struct slot`, that evaluation is refused
(`could not evaluate instance memory body`: the base's load reports a missing
view of the pool field). Without `object(other)` the same proof verifies.

The arena example meets this in `arena_reuse`, whose caller owns the
descriptor it allocates into beside the region it frees: its C reads
`middle->arena` only after `arena_free` has returned the descriptor.

```c filename=unfold_region_beside_an_object_of_its_type_frontier.c
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

verifying "unfold_region_beside_an_object_of_its_type_frontier.c";

int32 peek(struct slot* s, struct slot* other) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));
    owns object(other);
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
fail: could not evaluate instance memory body
```
