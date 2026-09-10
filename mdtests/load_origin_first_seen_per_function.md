# A load variable's origin is first-seen per verified function

A verdict must not depend on which other functions share the sidecar or on
their order. Load variables are named by content, so `reset_pipeline` and
`two_inits` mint the same variable for a pool's `capacity` after a call
havoc, and the registry records the live snapshot the variable was first
minted from as the origin fact transport resolves through. When that origin
was first seen while verifying `reset_pipeline`, it belongs to a memory DAG
that `two_inits`'s second call havoc never connects to, and `valid_pool(a)`
could not be carried across `pool_init(b, 1)`: the same file with
`two_inits` declared first verified. The origin is now first-seen within the
function being verified, so declaration order does not change the verdict.

```c filename=load_origin_first_seen_per_function.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_init(struct pool* pool, int32 capacity) {
    pool->checked_out = 0;
    pool->capacity = capacity;
}

void pool_reset(struct pool* pool) {
    pool->checked_out = 0;
    pool->capacity = 0;
}

void reset_pipeline(struct pool* pool) {
    pool_init(pool, 0);
    pool_reset(pool);
}

void two_inits(struct pool* a, struct pool* b) {
    pool_init(a, 1);
    pool_init(b, 1);
}
```

```click
resource pool_slot(pool: struct pool*) {
    views object(pool);
}

predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->capacity == pool->checked_out + count(pool_slot(pool))
}

verifying "load_origin_first_seen_per_function.c";

void pool_init(struct pool* pool, int32 capacity) {
    requires 0 <= capacity;
    owns object(pool);
    produces capacity of pool_slot(pool);
    ensures valid_pool(pool);
    ensures pool->capacity == capacity;
} by {
    execute();
    if 0 < capacity {
        fold(capacity of pool_slot(pool));
        simp();
    } else {
        apply(int32_ge_and_not_gt_implies_eq(capacity, 0)) using {
            0 <= capacity;
            not (0 < capacity);
        }
        simp();
    }
}

void pool_reset(struct pool* pool) {
    owns object(pool);
    ensures pool->capacity == 0;
} by auto;

void reset_pipeline(struct pool* pool) {
    owns object(pool);
    ensures pool->capacity == 0;
} by {
    step();
    step();
    step();
    simp();
}

void two_inits(struct pool* a, struct pool* b) {
    requires a != b;
    owns object(a);
    owns object(b);
    produces 1 of pool_slot(a);
    produces 1 of pool_slot(b);
    ensures valid_pool(a);
    ensures a->capacity == 1;
} by {
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
