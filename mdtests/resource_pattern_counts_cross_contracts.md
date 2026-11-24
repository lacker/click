# Resource-pattern counts cross opaque contracts

A wildcard resource count remains active when it is zero. Opaque calls that
produce or consume an exact matching resource update the aggregate count, so a
predicate relating C memory to that count can be re-established modularly.

Each member privately owns the exact abstract `available(object)` token.
Checkout transfers that token into the new member; return releases it while
consuming one member. Return accepts an arbitrary population total: custody of
one member supplies the decrement bound, without claiming that no other member
has the same object argument. The roundtrip restores the caller's token and
count predicate. All three C programs are unchanged.

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
authorized resource pool_object(pool: struct pool*, object: int32) {
    owns available(object);
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
    owns authority(pool_object(pool, _));
    consumes available(object);
    produces pool_object(pool, object);

    ensures valid_pool(pool);
} by {
    unfold(at(function.entry, valid_pool(pool)));
    have pool->checked_out == count(pool_object(pool, _));
    step();
    fold(pool_object(pool, object));
    have count(pool_object(pool, _)) == old(count(pool_object(pool, _))) + 1;
    have valid_pool(pool) by {
        unfold(valid_pool(pool));
        close();
    }
    step_until(function.exit);
    close();
}

void pool_return(struct pool* pool, int32 object) {
    requires valid_pool(pool);
    owns pool->checked_out;
    owns authority(pool_object(pool, _));
    consumes pool_object(pool, object);
    produces available(object);

    ensures valid_pool(pool);
} by {
    unfold(at(function.entry, valid_pool(pool)));
    have 1 <= pool->checked_out by {
        rewrite(pool->checked_out, count(pool_object(pool, _)));
        close() using { count(pool_object(pool, _)) >= 1; };
    }
    unfold(pool_object(pool, object));
}

void pool_roundtrip(struct pool* pool, int32 object) {
    requires valid_pool(pool);
    requires count(pool_object(pool, _)) < 2147483647;
    owns pool->checked_out;
    owns authority(pool_object(pool, _));
    owns available(object);

    ensures valid_pool(pool);
} by {
    unfold(at(function.entry, valid_pool(pool)));
    step();
    step();
}
```

```expect
pass
```
