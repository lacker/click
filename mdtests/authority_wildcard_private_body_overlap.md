# Two members cannot package the same owned memory

```c filename=wildcard_private_overlap.c
void lifecycle() {
    int32 pool = 0;
    int32* p = malloc(4);
    if (p == 0) return;
    free(p);
}
```

```click
authorized resource slot(pool: int32*, p: int32*, tag: int32) { owns p[0..1]; }
verifying "wildcard_private_overlap.c";
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step();
    branch { true => { step_until(function.exit); close(); } false => {} }
    fold(authority(slot(&pool, _, _)));
    fold(slot(&pool, p, 1));
    fold(slot(&pool, p, 2));
    unfold(slot(&pool, p, 1));
    unfold(authority(slot(&pool, _, _)));
    step_until(function.exit); close();
}
```

```expect
fail: Requires the private body of slot(p)
```
