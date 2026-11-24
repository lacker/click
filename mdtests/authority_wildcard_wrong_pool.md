# The authority for one pool cannot authorize births in another.

```c filename=wildcard_lifecycle.c
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
}
```

```click
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_lifecycle.c";
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _)));
    have count(slot(&pool, _)) == 0 by close();
    fold(slot(&first, &second));
    fold(slot(&pool, &second));
    have count(slot(&pool, _)) == 2 by close();
    unfold(slot(&pool, &first));
    have count(slot(&pool, _)) == 1 by close();
    unfold(slot(&pool, &second));
    have count(slot(&pool, _)) == 0 by close();
    unfold(authority(slot(&pool, _)));
}
```

```expect
fail: Requires owns authority(
```
