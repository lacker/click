struct pool {
    int32 checked_out;
    int32 capacity;
};

struct object {
    int32 value;
};

void pool_transfer(
    struct pool* source,
    struct pool* destination,
    struct object* object
) {
    source->checked_out = source->checked_out - 1;
    destination->checked_out = destination->checked_out + 1;
}
