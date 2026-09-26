# Unfolding a region beside an owned object of its type

`pool_slot(s)` owns the descriptor `object(s)` and `s->pool->data[at..end]`.
With the pool state unfolded, `peek` unfolds the slot to read through it, as
the arena's `arena_read` does, while it also owns `object(other)`, a second
`struct slot`. The unfold evaluates the slot body's range, whose base loads
`s->pool`, and that load must name the same pointer as `old(s->pool)`, the
pool the state was unfolded at.

Owning `object(other)` materializes its cells, `other->pool` among them: each
holds exactly the value a load of that cell reads, so a load of any other cell
is unchanged by them and is named at their common source. A pointer-valued
cell such as `other->pool` counts as such a materialization when its value is
the pointer a load of that same cell produces. Before it did, the reload of
`s->pool` got a second name, nothing related the two, and the unfold was
refused (`could not evaluate instance memory body`).

The arena example meets this shape in `arena_reuse`, whose caller owns the
descriptor it allocates into beside the region it frees.

```c filename=unfold_region_beside_an_object_of_its_type.c
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

verifying "unfold_region_beside_an_object_of_its_type.c";

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
pass
```
