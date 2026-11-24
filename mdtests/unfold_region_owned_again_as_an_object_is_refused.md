# Contradictory region ownership is still refused by raw contract validation

The contract owns `*s` both inside `pool_slot(s)` and beside it. Raw entry
admission rejects that duplicate before execution. Instance unfold exposes an
already-held body without searching its frame for overlap, and observation
does not repeat entry admission. Keep this refusal distinct from the unfold rule; the
positive control is `unfold_region_then_write_a_descriptor_of_its_type.md`.

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
    owns pool->data;
    owns pool->n;
    fact 0 <= live;
}

resource pool_slot(s: struct slot*) {
    field at: int32;
    field end: int32;
    owns *s;
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
    owns *s;
} by {
    let { live: n } = unfold(st);
    let { at: a, end: e } = unfold(r);
    step_until(function.exit);
    let r = fold(pool_slot(s), { at: a, end: e });
    let st = fold(pool_state(s->pool), { live: n });
    close();
}
```

```expect
fail: overlapping owned memory resource facts
```
