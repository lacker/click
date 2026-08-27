resource pool_object(
    pool: struct pool*,
    object: struct object*
) {
    owns object(object);
}

resource pool_slot(pool: struct pool*) {
    views object(pool);
}

predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(pool_object(pool, _)) and
    pool->capacity ==
        pool->checked_out + count(pool_slot(pool))
}

verifying "pool_init.c";
verifying "pool_checkout.c";
verifying "pool_transfer.c";
verifying "pool_transfer_pipeline.c";
verifying "pool_return.c";
verifying "pool_destroy.c";
verifying "pool_pipeline.c";
verifying "pool_zero_pipeline.c";

void pool_init(struct pool* pool, int32 capacity) {
    requires 0 <= capacity;
    owns object(pool);
    mutable pool->checked_out, pool->capacity;
    produces capacity of pool_slot(pool);

    ensures valid_pool(pool);
    ensures pool->capacity == capacity;
} by {
    execute();
    if 0 < capacity {
        fold(capacity of pool_slot(pool));
        frame();
        simp();
    } else {
        apply(int32_ge_and_not_gt_implies_eq(capacity, 0)) using {
            0 <= capacity;
            not (0 < capacity);
        }
        frame();
        simp();
    }
}

void pool_checkout(struct pool* pool, struct object* object) {
    requires valid_pool(pool);
    owns object(pool);
    consumes object(object);
    consumes pool_slot(pool);
    mutable pool->checked_out;
    produces pool_object(pool, object);

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    observe(pool_slot(pool));
    have 1 <= count(pool_slot(pool)) by {
        assumption();
    }
    have pool->capacity ==
        (pool->checked_out + 1) + (count(pool_slot(pool)) - 1) by {
        apply(int32_move_one_from_right_to_left_preserves_sum(
            pool->capacity,
            pool->checked_out,
            count(pool_slot(pool))
        )) using {
            0 <= pool->checked_out;
            1 <= count(pool_slot(pool));
            pool->capacity ==
                pool->checked_out + count(pool_slot(pool));
        }
        assumption();
    }
    execute();
    fold(pool_object(pool, object));
    frame();
    have count(pool_slot(pool)) ==
        at(statement(0).entry, count(pool_slot(pool))) - 1 by {
        simp();
    }
    have pool->checked_out ==
        at(statement(0).entry, pool->checked_out) + 1 by {
        simp();
    }
    have count(pool_object(pool, _)) ==
        at(statement(0).entry, count(pool_object(pool, _))) + 1 by {
        simp();
    }
    have pool->capacity == at(statement(0).entry, pool->capacity) by {
        simp();
    }
    have 0 <= pool->checked_out and
        pool->checked_out == count(pool_object(pool, _)) and
        pool->capacity == pool->checked_out + count(pool_slot(pool)) by {
        rewrite(at(statement(0).entry, pool->capacity) ==
            (at(statement(0).entry, pool->checked_out) + 1) +
            (at(statement(0).entry, count(pool_slot(pool))) - 1));
        rewrite(at(statement(0).entry, pool->checked_out) ==
            at(statement(0).entry, count(pool_object(pool, _))));
        normalize();
    }
    assumption();
    assumption();
    unfold(valid_pool);
    assumption();
}

void pool_return(struct pool* pool, struct object* object) {
    requires valid_pool(pool);
    requires count(pool_object(pool, object)) == 1;
    owns object(pool);
    consumes pool_object(pool, object);
    mutable pool->checked_out;
    produces object(object);
    produces pool_slot(pool);

    ensures valid_pool(pool);
} by {
    unfold(valid_pool);
    unfold(pool_object(pool, object));
    execute();
    frame();
    simp();
}

void pool_transfer(
    struct pool* source,
    struct pool* destination,
    struct object* object
) {
    requires source != destination;
    requires valid_pool(source);
    requires valid_pool(destination);
    requires count(pool_object(source, object)) == 1;
    requires count(pool_object(destination, object)) == 0;
    owns object(source);
    owns object(destination);
    consumes pool_object(source, object);
    consumes pool_slot(destination);
    mutable source->checked_out, destination->checked_out;
    produces pool_object(destination, object);
    produces pool_slot(source);

    ensures valid_pool(source);
    ensures valid_pool(destination);
} by {
    unfold(valid_pool);
    unfold(pool_object(source, object));
    observe(pool_slot(destination));
    have 1 <= count(pool_slot(destination)) by {
        assumption();
    }
    have destination->capacity ==
        (destination->checked_out + 1) +
        (count(pool_slot(destination)) - 1) by {
        apply(int32_move_one_from_right_to_left_preserves_sum(
            destination->capacity,
            destination->checked_out,
            count(pool_slot(destination))
        )) using {
            0 <= destination->checked_out;
            1 <= count(pool_slot(destination));
            destination->capacity ==
                destination->checked_out + count(pool_slot(destination));
        }
        assumption();
    }
    execute();
    fold(pool_object(destination, object));
    frame();
    simp();
}

void pool_destroy(struct pool* pool) {
    requires valid_pool(pool);
    requires pool->checked_out == 0;
    owns object(pool);
    consumes pool->capacity of pool_slot(pool);
    mutable pool->capacity;

    ensures valid_pool(pool);
    ensures pool->capacity == 0;
} by {
    unfold(valid_pool);
    observe(0 of pool_slot(pool));
    have pool->checked_out + count(pool_slot(pool)) ==
        count(pool_slot(pool)) by {
        rewrite(pool->checked_out == 0);
        normalize();
    }
    have pool->capacity == count(pool_slot(pool)) by {
        rewrite(pool->capacity ==
            pool->checked_out + count(pool_slot(pool)));
        rewrite(pool->checked_out + count(pool_slot(pool)) ==
            count(pool_slot(pool)));
        normalize();
    }
    have 0 <= pool->capacity by {
        rewrite(pool->capacity == count(pool_slot(pool)));
        assumption();
    }
    observe(pool->capacity of pool_slot(pool));
    execute();
    frame();
    simp();
}

void pool_zero_pipeline(struct pool* pool) {
    owns object(pool);
    mutable pool->checked_out, pool->capacity;

    ensures valid_pool(pool);
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
} by {
    step();
    step();
    execute();
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
    mark before_object_writes;
    open(pool_object(pool, first)) {
        step();
    }
    open(pool_object(pool, second)) {
        step();
    }
    transport(
        at(before_object_writes,
            0 <= pool->checked_out and
            pool->checked_out == count(pool_object(pool, _)) and
            pool->capacity ==
                pool->checked_out + count(pool_slot(pool))),
        0 <= pool->checked_out and
        pool->checked_out == count(pool_object(pool, _)) and
        pool->capacity ==
            pool->checked_out + count(pool_slot(pool))
    );
    mark after_object_writes;
    step();
    transport(
        at(after_object_writes, first->value == 11),
        first->value == 11
    );
    transport(
        at(after_object_writes, second->value == 22),
        second->value == 22
    );
    unfold(valid_pool);
    step();
    unfold(valid_pool);
    have pool->checked_out == 0 by simp;
    have pool->checked_out + count(pool_slot(pool)) ==
        count(pool_slot(pool)) by {
        rewrite(pool->checked_out == 0);
        normalize();
    }
    have pool->capacity == count(pool_slot(pool)) by {
        rewrite(pool->capacity ==
            pool->checked_out + count(pool_slot(pool)));
        rewrite(pool->checked_out + count(pool_slot(pool)) ==
            count(pool_slot(pool)));
        normalize();
    }
    have 0 <= pool->capacity by {
        rewrite(pool->capacity == count(pool_slot(pool)));
        assumption();
    }
    step();
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

void pool_transfer_pipeline(
    struct pool* source,
    struct pool* destination,
    struct object* object
) {
    requires source != destination;
    owns object(source);
    owns object(destination);
    owns object(object);
    mutable source->checked_out, source->capacity,
        destination->checked_out, destination->capacity;
    produces pool_object(destination, object);
    produces pool_slot(source);

    ensures valid_pool(source);
    ensures valid_pool(destination);
    ensures source->checked_out == 0;
    ensures source->capacity == 1;
    ensures destination->checked_out == 1;
    ensures destination->capacity == 1;
} by {
    step();
    step();
    unfold(valid_pool);
    mark pools_initialized;
    step();
    transport(
        at(pools_initialized,
            0 <= destination->checked_out and
            destination->checked_out == count(pool_object(destination, _)) and
            destination->capacity ==
                destination->checked_out + count(pool_slot(destination))),
        0 <= destination->checked_out and
        destination->checked_out == count(pool_object(destination, _)) and
        destination->capacity ==
            destination->checked_out + count(pool_slot(destination))
    );
    step();
    step();
    frame();
    simp();
}
