struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_shrink(struct pool* pool, int32 amount) {
    pool->capacity = pool->capacity - amount;
}
