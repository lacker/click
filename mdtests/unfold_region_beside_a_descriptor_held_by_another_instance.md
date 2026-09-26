# Unfolding a region beside a descriptor another instance holds

The companion of `unfold_region_beside_an_object_of_its_type.md` in which the
second `struct slot` is owned through an instance of its own, `slot_desc`,
rather than flat. The proof unfolds that instance first, so its descriptor's
cells are owned beside the folded region when the region is unfolded, and the
region's body still reads `s->pool` at the pool the state was unfolded at.

```c filename=unfold_region_beside_a_descriptor_held_by_another_instance.c
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

resource slot_desc(d: struct slot*) {
    field at: int32;
    owns object(d);
    fact d->at == at;
}

verifying "unfold_region_beside_a_descriptor_held_by_another_instance.c";

int32 peek(struct slot* s, struct slot* other) {
    owns r: pool_slot(s);
    owns st: pool_state(old(s->pool));
    owns o: slot_desc(other);
} by {
    let { at: oa } = unfold(o);
    let { live: n } = unfold(st);
    let { at: a, end: e } = unfold(r);
    execute();
    let r = fold(pool_slot(s), { at: a, end: e });
    let st = fold(pool_state(s->pool), { live: n });
    let o = fold(slot_desc(other), { at: oa });
    simp();
}
```

```expect
pass
```
