# A lease is tied to the pool that issued it

```c filename=cycle.c
void cycle(int32* (*acquire)(int32*), void (*release)(int32*, int32*), int32* pool, int32* other) {
    int32* cell = acquire(pool);
    if (cell != 0) {
        *cell = 7;
        release(other, cell);
    }
}
```

```click
abstract resource Available(pool: int32*);
abstract resource Lease(pool: int32*, cell: int32*);
resource Acquisition(pool: int32*, cell: int32*) {
    if cell != 0 {
        owns cell[0..1];
        owns Lease(pool, cell);
        fact cell == pool;
    }
}
resource Unavailable(pool: int32*, cell: int32*) {
    if cell == 0 {
        owns Available(pool);
    }
}
contract int32* Acquire(int32* pool) {
    consumes Available(pool);
    produces Acquisition(pool, result);
    produces Unavailable(pool, result);
}
contract void Release(int32* pool, int32* cell) {
    consumes Lease(pool, cell);
    consumes cell[0..1];
    produces Available(pool);
}
verifying "cycle.c";
void cycle(int32* (*acquire)(int32*), void (*release)(int32*, int32*), int32* pool, int32* other) {
    requires pool != other;
    requires Acquire(acquire);
    requires Release(release);
    owns Available(pool);
} by {
    step();
    step(Acquire);
    if c(cell) != 0 {
        unfold(Acquisition(pool, c(cell)));
        unfold(Unavailable(pool, c(cell)));
        step();
        step();
        step(Release);
        execute(); simp();
    } else {
        unfold(Acquisition(pool, c(cell)));
        unfold(Unavailable(pool, c(cell)));
        execute(); simp();
    }
}
```

```expect
fail: missing resource
```
