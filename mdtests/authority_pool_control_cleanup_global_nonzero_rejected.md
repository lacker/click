# Cleanup cannot infer global emptiness from owning no slots

This helper owns the control and no slots. Its authenticated entry count
is one, so exhausting its local ownership cannot justify retiring authority.
Writing the C capacity field to zero does not change the population.

```c filename=pool_destroy.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_destroy(struct pool* pool) {
    pool->capacity = 0;
}
```

```c filename=payload.c
struct object { int32 value; };
```

```click
authorized resource pool_slot(pool: struct pool*) {}
authorized resource pool_object(pool: struct pool*, object: struct object*) { owns *object; }
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(pool_object(pool, _));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(pool_object(pool, _)) and
    pool->capacity == pool->checked_out + count(pool_slot(pool))
}
verifying "pool_destroy.c";
verifying "payload.c";
void pool_destroy(struct pool* pool) {
    consumes pool_control(pool);
    requires pool->checked_out == 0;
    requires pool->capacity == 1;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_control(pool));
    have count(pool_object(pool, _)) == 0 by close();
    have pool->capacity == count(pool_slot(pool)) by close();
    step();
    unfold(authority(pool_slot(pool)));
    unfold(authority(pool_object(pool, _)));
    step_until(function.exit); unfold(valid_pool(pool)); close();
}
```

```expect
fail: Requires count(pool_slot(...)) == 0 and no outstanding member custody before authority retirement
```
