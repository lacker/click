resource pool_object(
    pool: struct pool*,
    object: struct object*
) {
    owns object(object);
}

predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out <= pool->capacity and
    pool->checked_out == count(pool_object(pool, _))
}

verifying "pool_init.c";
verifying "pool_checkout.c";
verifying "pool_return.c";
verifying "pool_destroy.c";
verifying "pool_pipeline.c";

void pool_init(struct pool* pool, int32 capacity) {
    requires 0 <= capacity;
    owns object(pool);
    mutable pool->checked_out, pool->capacity;

    ensures valid_pool(pool);
    ensures pool->capacity == capacity;
} by {
    execute();
    have valid_pool(pool) by {
        unfold(valid_pool);
        simp();
    }
    frame();
    simp();
}

void pool_checkout(struct pool* pool, struct object* object) {
    requires valid_pool(pool);
    requires pool->checked_out < pool->capacity;
    owns object(pool);
    consumes object(object);
    mutable pool->checked_out;
    produces pool_object(pool, object);

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    execute();
    fold(pool_object(pool, object));
    have valid_pool(pool) by {
        unfold(valid_pool);
        simp();
    }
    frame();
    simp();
}

void pool_return(struct pool* pool, struct object* object) {
    requires valid_pool(pool);
    requires count(pool_object(pool, object)) == 1;
    owns object(pool);
    consumes pool_object(pool, object);
    mutable pool->checked_out;
    produces object(object);

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    unfold(pool_object(pool, object));
    execute();
    frame();
    simp();
}

void pool_destroy(struct pool* pool) {
    requires valid_pool(pool);
    requires pool->checked_out == 0;
    owns object(pool);
    mutable pool->capacity;

    ensures valid_pool(pool);
    ensures pool->capacity == 0;
} by {
    unfold(valid_pool);
    execute();
    have valid_pool(pool) by {
        unfold(valid_pool);
        simp();
    }
    frame();
    simp();
}

void pool_pipeline(
    struct pool* pool,
    struct object* first,
    struct object* second
) {
    owns object(pool);
    owns object(first);
    owns object(second);
    mutable pool->checked_out, pool->capacity, first->value, second->value;

    ensures valid_pool(pool);
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures first->value == 11;
    ensures second->value == 22;
} by {
    step();
    step();
    step();
    unfold(valid_pool);
    open(pool_object(pool, first)) {
        step() using {
            0 <= pool->checked_out;
            pool->checked_out <= pool->capacity;
            pool->checked_out == count(pool_object(pool, _));
        }
    }
    open(pool_object(pool, second)) {
        step() using {
            0 <= pool->checked_out;
            pool->checked_out <= pool->capacity;
            pool->checked_out == count(pool_object(pool, _));
        }
    }
    mark after_object_writes;
    step() using {
        loadable(pool->checked_out);
        loadable(pool->capacity);
        0 <= pool->checked_out;
        pool->checked_out <= pool->capacity;
        pool->checked_out == count(pool_object(pool, _));
    }
    transport(
        at(after_object_writes, first->value == 11),
        first->value == 11
    );
    transport(
        at(after_object_writes, second->value == 22),
        second->value == 22
    );
    unfold(valid_pool);
    step() using {
        loadable(pool->checked_out);
        loadable(pool->capacity);
        0 <= pool->checked_out;
        pool->checked_out <= pool->capacity;
        pool->checked_out == count(pool_object(pool, _));
    }
    unfold(valid_pool);
    have pool->checked_out == 0 by simp;
    step() using {
        loadable(pool->checked_out);
        loadable(pool->capacity);
        0 <= pool->checked_out;
        pool->checked_out <= pool->capacity;
        pool->checked_out == count(pool_object(pool, _));
        pool->checked_out == 0;
        first->value == 11;
        second->value == 22;
    }
    step();
    frame();
    have pool->capacity == 0 by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}
