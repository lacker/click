# A call keeps a region beside a folded arena state it lends

The shape of `examples/arena`'s pipeline, reduced. `pool_state` is a folded
field-bearing state whose field-free `pool_cells` child owns a flag map and,
through an iterated clause, every free data cell; `pool_slot` is a
field-bearing region that owns its descriptor and `pool->data[at..end]`.
`two_puts` writes `11` through `first`, then `22` through `second`, then
reads the first value back, lending the state and one region to each call.

Each call's footprint is the whole data buffer (the iterated clause counts
every element it could hold), so a call used to drop the value written
through `first` when it lent the state with `second`. The caller keeps
`first`'s region outside that transfer, and owned memory is a partition at
the call, so the callee can write none of it. The call havoc opens the
residual `pool_slot` one body layer, and its own facts (`s->at == at`)
place the cell `pool->data[first->at]` in the range spelled through its
field. The value `put` wrote is carried across the second call with
`transport`, whose frame evidence is the kept range; `pool->data` is
reloaded after the call, and `put`'s `pool->data == old(pool->data)` relates
the two spellings of the base.

```c filename=call_keeps_region_beside_folded_arena_state.c
struct pool {
    int32* data;
    int32* flags;
    int32 n;
};

struct slot {
    int32 at;
    int32 end;
};

void put(struct pool* pool, struct slot* s, int32 value) {
    pool->data[s->at] = value;
}

int32 get(struct pool* pool, struct slot* s) {
    return pool->data[s->at];
}

int32 two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    put(pool, first, 11);
    put(pool, second, 22);
    return get(pool, first);
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

resource pool_slot(s: struct slot*, pool: struct pool*) {
    field at: int32;
    field end: int32;
    owns object(s);
    owns pool->data[at..end];
    fact s->at == at;
    fact s->end == end;
    fact 0 <= at;
    fact at < end;
}

verifying "call_keeps_region_beside_folded_arena_state.c";

void put(struct pool* pool, struct slot* s, int32 value) {
    owns st: pool_state(pool);
    owns r: pool_slot(s, pool);

    ensures r.at == old(r.at);
    ensures r.end == old(r.end);
    ensures st.live == old(st.live);
    ensures pool->data == old(pool->data);
    ensures pool->data[s->at] == value;
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
    let r = fold(pool_slot(s, pool), { at: a, end: e });
    let st = fold(pool_state(pool), { live: n });
    simp();
}

int32 get(struct pool* pool, struct slot* s) {
    owns st: pool_state(pool);
    owns r: pool_slot(s, pool);

    ensures r.at == old(r.at);
    ensures r.end == old(r.end);
    ensures st.live == old(st.live);
    ensures pool->data == old(pool->data);
    ensures pool->data[s->at] == old(pool->data[s->at]);
    ensures result == pool->data[s->at];
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
    let r = fold(pool_slot(s, pool), { at: a, end: e });
    let st = fold(pool_state(pool), { live: n });
    simp();
}

int32 two_puts(struct pool* pool, struct slot* first, struct slot* second) {
    owns st: pool_state(pool);
    owns a: pool_slot(first, pool);
    owns b: pool_slot(second, pool);

    ensures result == 11;
} by {
    step(put(pool, first, 11), { st: st, r: a });
    have pool->data[first->at] == 11 by simp;
    mark m1;
    step(put(pool, second, 22), { st: st, r: b });
    have pool->data == at(m1, pool->data) by simp;
    have pool->data[first->at] == 11 by {
        transport(at(m1, pool->data[first->at]) == 11, pool->data[first->at] == 11) using {
            at(m1, pool->data[first->at]) == 11;
            pool->data == at(m1, pool->data);
        }
    }
    step(get(pool, first), { st: st, r: a });
    execute();
    simp();
}
```

```expect
pass
```
