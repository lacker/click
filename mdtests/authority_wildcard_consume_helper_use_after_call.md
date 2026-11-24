# A consumed member is unavailable to the caller

```c filename=wildcard_consume_use_after_call.c
void release(int32* pool, int32* member) {}
void lifecycle() {
    int32 pool = 0;
    int32 member = 0;
    release(&pool, &member);
}
```

```click
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_consume_use_after_call.c";
void release(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    consumes slot(pool, member);
} by { unfold(slot(pool, member)); }
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, &member));
    step();
    have count(slot(&pool, _)) == 0 by close();
    unfold(slot(&pool, &member));
    unfold(authority(slot(&pool, _)));
}
```

```expect
fail: Requires owns slot
```
