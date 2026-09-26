# Unfolding a region after writing through another descriptor's pool

The two-hop variant of `unfold_region_after_writing_a_descriptor_of_its_type.md`.
The store is `q->n = 3` with `q` loaded from `other->pool`, so its address is
based two loads away from a parameter, and it is owned flat through
`other->pool->n`. The cells the store must keep are two folded
instances' own: `s->pool` inside the region `r`, and `pool->n` inside the pool
state `st`, whose argument is the pool loaded from `s`. Each is a cell one
body layer inside an instance whose argument names the cell's base, and each
instance is a different owned member than the one holding the written bytes,
so the partition law keeps both. The state and the region then unfold at the
names they were folded at, and `pool->n` still reads its entry value.

```c filename=unfold_region_after_writing_through_another_descriptors_pool.c
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
    struct pool* q;

    q = other->pool;
    q->n = 3;
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

verifying "unfold_region_after_writing_through_another_descriptors_pool.c";

int32 peek(struct slot* s, struct slot* other) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));
    owns object(other);
    owns other->pool->n;
    ensures result == old(s->pool->n);
} by {
    step();
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
