# Each wildcard member maintains its own private invariant

Two slots occupy different cells of one backing allocation. Updating the first
preserves membership and the second cell's value.

```c filename=wildcard_body_facts.c
int32 lifecycle() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    p[0] = 7;
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click
authorized resource slot(pool: int32*, p: int32*) {
    owns p[0..1];
    fact 0 <= p[0];
    fact p[1] == 2;
}
verifying "wildcard_body_facts.c";
int32 lifecycle() { ensures result == 0 or result == 9; } by {
    step(); step(); step(); step();
    branch { true => { } false => {} }
    step(); step();
    fold(authority(slot(&pool, _)));
    have 0 <= p[0] by close();
    have 0 <= p[1] by close();
    have p[1] == 2 by close();
    fold(slot(&pool, p));
    fold(slot(&pool, p + 1));
    have count(slot(&pool, _)) == 2 by close();
    with(slot(&pool, p)) { step(); have 0 <= p[0] by close(); }
    have count(slot(&pool, _)) == 2 by close();
    with(slot(&pool, p)) {
        with(slot(&pool, p + 1)) { step(); step(); }
    }
    unfold(slot(&pool, p));
    unfold(slot(&pool, p + 1));
    unfold(authority(slot(&pool, _)));
}
```

```expect
fail: resource `slot` fact reads `p[1]` without a covering contained memory resource
```
