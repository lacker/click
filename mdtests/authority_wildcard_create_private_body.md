# A helper creates a member from supplied private memory

The caller retains another member while the helper exchanges owned memory
for a new member. The arbitrary entry population total increases by one.

```c filename=wildcard_create_private_body.c
void issue(int32* pool, int32* p) { p[0] = 7; }
int32 lifecycle() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    issue(&pool, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_create_private_body.c";
void issue(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes p[0..1];
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, p);
    ensures p[0] == 7;
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) + 1;
} by {
    step();
    fold(slot(pool, p));
}
int32 lifecycle() { ensures result == 0 or result == 9; } by {
    step(); step(); step(); step();
    branch { true => { step_until(function.exit); close(); } false => {} }
    step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, p + 1));
    step();
    have count(slot(&pool, _)) == 2;
    with(slot(&pool, p)) {
        with(slot(&pool, p + 1)) { step(); step(); }
    }
    unfold(slot(&pool, p));
    unfold(slot(&pool, p + 1));
    unfold(authority(slot(&pool, _)));
}
```

```expect
pass
```
