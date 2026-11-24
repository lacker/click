# Original pool checkout cannot manufacture an available slot

The C block is unchanged from `examples/bounded-pool/pool_checkout.c`.
A control with no available slots cannot justify checkout.

```c filename=pool_checkout.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

struct object {
    int32 value;
};

void pool_checkout(struct pool* pool, struct object* object) {
    pool->checked_out = pool->checked_out + 1;
}
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
verifying "pool_checkout.c";
void pool_checkout(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    requires count(pool_slot(pool)) == 0;
    consumes *object;
    produces pool_object(pool, object);
    ensures count(pool_slot(pool)) == old(count(pool_slot(pool))) - 1;
    ensures count(pool_object(pool, _)) == old(count(pool_object(pool, _))) + 1;
    ensures to_integer(pool->checked_out) == to_integer(old(pool->checked_out) + 1);
    ensures pool->capacity == old(pool->capacity);
    ensures valid_pool(pool);
} by {
    with(pool_control(pool)) {
        have 1 <= count(pool_slot(pool)) by close();
    }
    step_until(function.exit); unfold(valid_pool(pool)); close();
}

```

```expect
fail: could not establish `1 <= to_integer(count(pool_slot(pool)))`
```
