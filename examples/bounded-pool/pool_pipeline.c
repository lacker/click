struct pool {
    int32 checked_out;
    int32 capacity;
};

struct object {
    int32 value;
};

void pool_pipeline(
    struct pool* pool,
    struct object* first,
    struct object* second
) {
    pool_init(pool, 2);
    pool_checkout(pool, first);
    pool_checkout(pool, second);
    first->value = 11;
    second->value = 22;
    pool_return(pool, second);
    pool_return(pool, first);
    pool_destroy(pool);
}
