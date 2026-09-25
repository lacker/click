# A call keeps a region cell the caller reads through its descriptor

The shape of `examples/arena`'s pipeline at its first read, reduced. The
folded `pool_state` spans the whole data buffer through its iterated clause;
`pool_slot(s)` takes the descriptor alone, owns it and `s->pool->data[at..end]`,
so the data cell a region owns is addressed in two hops, through the
descriptor's `pool` field and then the pool's `data` field. `two_puts` writes
`11` through `first`, then `22` through `second`, lending the state and
`second`'s region, then reads `first`'s cell back through `get`.

The caller keeps `first`'s region outside the second call, so the call havoc
keeps its cell (`call_keeps_region_beside_folded_arena_state.md` is the
one-hop form). The proof carries the value across the call with an explicit
`transport` whose frame evidence is the kept range, after relating both address
loads to their pre-call values; the pointer-level links compose as in
`simp_composes_a_pointer_field_chain_across_a_call.md`.

`simp` does not find this step on its own, and is not asked to. Rewriting the
two address loads to their pre-call spellings leaves the goal's current load
reading a naming projection that was recorded for the old address spelling,
so the projection route cannot lead it back to the snapshot it came from, and
the kept-by-caller crossing is an assumption-dependent hop that the typed
load-equality routes do not consume. The explicit `transport` is the
supported step.

```c filename=call_keeps_a_region_cell_read_through_its_descriptor.c
struct pool {
    int32* data;
    int32* flags;
    int32 n;
};

struct slot {
    struct pool* pool;
    int32 at;
    int32 end;
};

void put(struct slot* s, int32 value) {
    struct pool* pool;

    pool = s->pool;
    pool->data[s->at] = value;
}

int32 get(struct slot* s) {
    struct pool* pool;

    pool = s->pool;
    return pool->data[s->at];
}

void attach(struct pool* pool, struct slot* first, struct slot* second) {
    first->pool = pool;
    first->at = 0;
    first->end = 1;
    second->pool = pool;
    second->at = 1;
    second->end = 2;
}

int32 two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    attach(pool, first, second);
    put(first, 11);
    put(second, 22);
    return get(first);
}
```

```click
resource pool_cells(data: int32*, flags: int32*, n: int32) {
    owns flags[0..n];
    forall (k: int32) where 0 <= k and k < n {
        if flags[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource pool_state(pool: struct pool*) {
    field live: int32;
    owns &pool->data;
    owns &pool->flags;
    owns pool->n;
    owns pool_cells(pool->data, pool->flags, pool->n);
    fact 0 <= live;
    fact pool->n <= 536870911;
    fact separate(memory(pool->flags[0..pool->n]), memory(pool->data[0..pool->n]));
    fact separate(memory(object(pool)), memory(pool->data[0..pool->n]));
    fact separate(memory(object(pool)), memory(pool->flags[0..pool->n]));
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

verifying "call_keeps_a_region_cell_read_through_its_descriptor.c";

void put(struct slot* s, int32 value) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));

    ensures r.at == old(r.at);
    ensures r.end == old(r.end);
    ensures st.live == old(st.live);
    ensures s->pool == old(s->pool);
    ensures s->pool->data == old(s->pool->data);
    ensures s->pool->data[s->at] == value;
} by {
    let { live: n } = unfold(st);
    let { at: a, end: e } = unfold(r);
    have a + 1 <= e by {
        apply(int32_increment_upper_bound(a, e)) using {
            a < e;
        }
    }
    have s->at == a by {
        assumption();
    }
    have s->at + 1 <= e by {
        rewrite(s->at == a);
        assumption();
    }
    execute();
    let r = fold(pool_slot(s), { at: a, end: e });
    let st = fold(pool_state(s->pool), { live: n });
    simp();
}

int32 get(struct slot* s) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));

    ensures r.at == old(r.at);
    ensures r.end == old(r.end);
    ensures st.live == old(st.live);
    ensures s->pool == old(s->pool);
    ensures result == old(s->pool->data[s->at]);
} by {
    let { live: n } = unfold(st);
    let { at: a, end: e } = unfold(r);
    have a + 1 <= e by {
        apply(int32_increment_upper_bound(a, e)) using {
            a < e;
        }
    }
    have s->at == a by {
        assumption();
    }
    have s->at + 1 <= e by {
        rewrite(s->at == a);
        assumption();
    }
    execute();
    let r = fold(pool_slot(s), { at: a, end: e });
    let st = fold(pool_state(s->pool), { live: n });
    simp();
}

void attach(struct pool* pool, struct slot* first, struct slot* second) {
    owns st: pool_state(pool);
    consumes object(first);
    consumes object(second);
    consumes pool->data[0..2];
    produces a: pool_slot(first);
    produces b: pool_slot(second);
    ensures st.live == old(st.live);
    ensures pool->data == old(pool->data);
    ensures first->pool == pool;
    ensures second->pool == pool;
} by {
    let { live: n } = unfold(st);
    execute();
    let a = fold(pool_slot(first), { at: 0, end: 1 });
    let b = fold(pool_slot(second), { at: 1, end: 2 });
    let st = fold(pool_state(pool), { live: n });
    simp();
}

int32 two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    owns st: pool_state(pool);
    consumes object(first);
    consumes object(second);
    consumes pool->data[0..2];

    ensures result == 11;
} by {
    let { a: a, b: b } = step(attach(pool, first, second), { st: st });
    step(put(first, 11), { st: st, r: a });
    have first->pool == pool by simp;
    have second->pool == pool by simp;
    mark m1;
    step(put(second, 22), { st: st, r: b });
    have first->pool == at(m1, first->pool) by simp;
    have first->at == at(m1, first->at) by simp;
    have second->pool == pool by simp;
    have first->pool == pool by simp;
    have first->pool->data == second->pool->data by {
        rewrite(first->pool == pool);
        rewrite(second->pool == pool);
        normalize();
    }
    have second->pool->data == at(m1, second->pool->data) by simp;
    have at(m1, second->pool->data) == at(m1, first->pool->data) by simp;
    have first->pool->data == at(m1, first->pool->data) by simp;
    have at(m1, first->pool->data[first->at]) == 11 by simp;
    have first->pool->data[first->at] == 11 by {
        transport(at(m1, first->pool->data[first->at]) == 11, first->pool->data[first->at] == 11) using {
            at(m1, first->pool->data[first->at]) == 11;
            first->pool->data == at(m1, first->pool->data);
            first->at == at(m1, first->at);
        }
    }
    step(get(first), { st: st, r: a });
    execute();
    simp();
}
```

```expect
pass
```
