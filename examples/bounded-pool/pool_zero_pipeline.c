struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_zero_pipeline(struct pool* pool) {
    pool_init(pool, 0);
    pool_destroy(pool);
}
