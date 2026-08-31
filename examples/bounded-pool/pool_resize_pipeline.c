struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_resize_pipeline(struct pool* pool) {
    pool_init(pool, 1);
    pool_shrink(pool, 1);
    pool_destroy(pool);
}
