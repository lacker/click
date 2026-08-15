# Resource-pattern counts cross opaque contracts

A wildcard resource count remains active when it is zero. Opaque calls that
produce or consume an exact matching resource update the aggregate count, so a
predicate relating C memory to that count can be re-established modularly.

```c filename=resource_pattern_count_checkout.c
struct pool {
    int32 checked_out;
};

void pool_checkout(struct pool* pool, int32 object) {
    pool->checked_out = pool->checked_out + 1;
}
```

```c filename=resource_pattern_count_return.c
struct pool {
    int32 checked_out;
};

void pool_return(struct pool* pool, int32 object) {
    pool->checked_out = pool->checked_out - 1;
}
```

```c filename=resource_pattern_count_roundtrip.c
struct pool {
    int32 checked_out;
};

void pool_roundtrip(struct pool* pool, int32 object) {
    pool_checkout(pool, object);
    pool_return(pool, object);
}
```

```click
abstract resource available(object: int32);
resource pool_object(pool: struct pool*, object: int32) {
    contains available(object);
}

predicate valid_pool(pool: struct pool*) {
    pool->checked_out == count(pool_object(pool, _))
}

verifying "resource_pattern_count_checkout.c";
verifying "resource_pattern_count_return.c";
verifying "resource_pattern_count_roundtrip.c";

void pool_checkout(struct pool* pool, int32 object) {
    requires valid_pool(pool);
    requires count(pool_object(pool, _)) < 2147483647;
    owns pool->checked_out;
    consumes available(object);
    produces pool_object(pool, object);
    mutable pool->checked_out;

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    execute();
    fold(pool_object(pool, object));
    have valid_pool(pool) by {
        unfold(valid_pool);
        simp();
    }
    frame();
    simp();
}

void pool_return(struct pool* pool, int32 object) {
    requires valid_pool(pool);
    requires count(pool_object(pool, object)) == 1;
    owns pool->checked_out;
    consumes pool_object(pool, object);
    produces available(object);
    mutable pool->checked_out;

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    unfold(pool_object(pool, object));
    execute();
    frame();
    simp();
}

void pool_roundtrip(struct pool* pool, int32 object) {
    requires valid_pool(pool);
    requires count(pool_object(pool, _)) < 2147483647;
    owns pool->checked_out;
    owns available(object);

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    step();
    step();
    execute();
    simp();
}
```

```expect
pass
```
