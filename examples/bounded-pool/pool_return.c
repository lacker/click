struct pool {
    int32 checked_out;
    int32 capacity;
};

struct object {
    int32 value;
};

void pool_return(struct pool* pool, struct object* object) {
    pool->checked_out = pool->checked_out - 1;
}
