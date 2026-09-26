# Unfolding an instance beside a viewed contract clause

A `views` clause records a loan dependency in the resource context and a
mirror of it in the state, and every rewrite checks that the two are the same
record. Removing the unfolded instance removes no loan dependency, so the
record must be left as it is; minting a fresh one detached the context from
the state's mirror and refused every unfold in a function with a `views`
clause.

```c filename=unfold_beside_a_views_clause.c
struct pool {
    int32* data;
    int32 n;
};

int32 get(struct pool* p, int32* q) {
    return p->n;
}
```

```click
resource pool_state(pool: struct pool*) {
    field live: int32;
    owns &pool->data;
    owns pool->n;
    fact 0 <= live;
}

verifying "unfold_beside_a_views_clause.c";

int32 get(struct pool* p, int32* q) {
    owns st: pool_state(p);
    views q[0..1];
} by {
    let { live: n } = unfold(st);
    execute();
    let st = fold(pool_state(p), { live: n });
    simp();
}
```

```expect
pass
```
