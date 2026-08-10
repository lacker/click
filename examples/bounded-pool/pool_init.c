struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_init(struct pool* pool, int32 capacity) {
    pool->checked_out = 0;
    pool->capacity = capacity;
}
