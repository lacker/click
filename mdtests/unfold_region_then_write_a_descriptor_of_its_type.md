# Writing another descriptor of the region's type after unfolding it

The region is unfolded while the second `struct slot` still holds its
materialized cells, then the C writes that descriptor's `at` and `pool`
fields. The descriptor `*s` and `*other` are then two owned
members of the frame, so the writes leave `s->pool` in place. The proof
explicitly preserves the backing `data` pointer across each store, allowing
the fold to consume the range the unfold produced.

```c filename=unfold_region_then_write_a_descriptor_of_its_type.c
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

verifying "unfold_region_then_write_a_descriptor_of_its_type.c";

int32 peek(struct slot* s, struct slot* other) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));
    owns *other;
} by {
    let { live: n } = unfold(st);
    let { at: a, end: e } = unfold(r);
    step();
    step();
    step();
    step_until(function.exit);
    have s->pool == old(s->pool) by { close(); }
    have at(statement(1).entry, s->pool->data) == old(s->pool->data) by { close(); }
    have separate(memory(*other), memory(s->pool->data)) by { close(); }
    have separate(memory(other->at), memory(s->pool->data)) by { close(); }
    have separate(statement(1).footprint, memory(s->pool->data)) by {
        close() using { separate(memory(other->at), memory(s->pool->data)); };
    }
    have at(statement(1).exit, s->pool->data) == at(statement(1).entry, s->pool->data) by {
        preserve(memory(s->pool->data), statement(1));
    }
    have separate(memory(other->pool), memory(s->pool->data)) by { close(); }
    have separate(statement(2).footprint, memory(s->pool->data)) by {
        close() using { separate(memory(other->pool), memory(s->pool->data)); };
    }
    have at(statement(2).exit, s->pool->data) == at(statement(2).entry, s->pool->data) by {
        preserve(memory(s->pool->data), statement(2));
    }
    have s->pool->data == at(statement(2).exit, s->pool->data) by { close(); }
    have s->pool->data == old(s->pool->data) by { close(); }
    let r = fold(pool_slot(s), { at: a, end: e });
    let st = fold(pool_state(s->pool), { live: n });
    close();
}
```

```expect
pass
```
