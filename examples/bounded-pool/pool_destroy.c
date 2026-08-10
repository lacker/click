struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_destroy(struct pool* pool) {
    pool->capacity = 0;
}
