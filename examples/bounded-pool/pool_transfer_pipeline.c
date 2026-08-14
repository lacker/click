struct pool {
    int32 checked_out;
    int32 capacity;
};

struct object {
    int32 value;
};

void pool_transfer_pipeline(
    struct pool* source,
    struct pool* destination,
    struct object* object
) {
    pool_init(source, 1);
    pool_init(destination, 1);
    pool_checkout(source, object);
    pool_transfer(source, destination, object);
}
